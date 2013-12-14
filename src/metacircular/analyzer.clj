(ns metacircular.analyzer)

(def special-operators
  '#{def defmacro fn if quote set!})

(defn special-operator? [x]
  (contains? special-operators x))

(defn special-form? [form]
  (boolean
   (and (seq? form)
        (when-first [op form]
          (special-operator? op)))))

(defn constant? [x]
  (or (nil? x)
      (true? x)
      (false? x)
      (number? x)
      (string? x)
      (char? x)
      (keyword? x)
      (and (seq? x) (empty? x))
      (instance? clojure.lang.IType x)
      (instance? clojure.lang.IRecord x)))

(defn find-index
  "Return the index into the frames stack for the frame containing sym."
  [env sym]
  (loop [frames (:locals env)]
    (when (seq frames)
      (let [frame (peek frames)]
        (if (contains? frame sym)
          (dec (count frames))
          (recur (pop frames)))))))

(defn has-local? [env sym]
  (not (nil? (find-index env sym))))

(defn has-var? [env sym]
  (contains? (:vars env) sym))

(defmulti parse
  "Parse a special form or invokation and return a map."
  (fn [[op & args :as form] env] op))

(declare analyze analyze-in)

(defmethod parse 'if
  [[op test then else :as form] env]
  {:pre [(= (count form) 4)]}
  (let [env (assoc env :context :expr)]
    {:op 'if
     :form form
     :env env
     :test (analyze test env)
     :then (analyze then env)
     :else (analyze else env)}))

(defn valid-fn-form?
  [form]
  (let [[one two three] form
        [name arg-list] (if (symbol? two)
                          [two three]
                          [nil two])]
    (and (= (first form) 'fn)
         (vector? arg-list)
         (every? symbol? arg-list))))

(defn parse-arg-list
  [arg-list]
  (let [[pos more] (split-with (complement '#{&}) arg-list)
        variadic (if-let [excess (nnext more)]
                   (throw (Exception. (str "Unexpected args: " excess)))
                   (when (seq more)
                     (second more)))
        n-pos (count pos)]
    {:positionals (vec pos)
     :variadic variadic
     :min-args n-pos
     :max-args (if variadic Integer/MAX_VALUE n-pos)}))

(defn parse-definition
  [form env]
  (let [name (let [maybe-name (second form)]
               (when (symbol? maybe-name)
                 maybe-name))
        [arg-list & body] (if name
                            (nnext form)
                            (next form))
        arg-spec (parse-arg-list arg-list)]
    (merge
     {:name name
      :form form
      :arg-list arg-list
      :arg-spec arg-spec}
     (let [syms (let [arg-syms (remove '#{&} arg-list)]
                  (if name
                    (conj arg-syms name)
                    arg-syms))
           env (-> env
                   (assoc :context :expr)
                   (update-in [:locals] conj (set syms)))]
       {:body {:statements (mapv (analyze-in env) (butlast body))
               :return (analyze (last body) env)}}))))

(defmethod parse 'fn
  [[op & more :as form] env]
  {:pre [(valid-fn-form? form)]}
  (let [env (assoc env :context :expr)]
    (merge
     {:op 'fn
      :env env}
     (parse-definition form env))))

(defmethod parse 'defmacro
  [[op target arg-list & body :as form] env]
  {:pre [(symbol? target)
         (vector? arg-list)
         (every? symbol? arg-list)
         (= (:context env) :toplevel)]}
  (let [env (assoc env :context :expr)]
    (merge
     {:op 'defmacro
      :form form
      :env env
      :target target}
     (parse-definition form env))))

(defmethod parse 'def
  [[op target expr :as form] env]
  {:pre [(symbol? target)
         (= (count form) 3)
         (= (:context env) :toplevel)]}
  (let [env (assoc env :context :expr)]
    {:op 'def
     :form form
     :env env
     :target target
     :expr (analyze expr env)}))

(defmethod parse 'set!
  [[op target expr :as form] env]
  {:pre [(symbol? target)
         (= (count form) 3)
         (has-local? env target)]}
  (let [env (assoc env :context :expr)]
    {:op 'set!
     :form form
     :env env
     :target target
     :expr (analyze expr env)}))

(defmethod parse 'quote
  [[op expr & _ :as form] env]
  (let [env (assoc env :context :expr)]
    {:op 'quote
     :form form
     :env env
     :expr expr}))

(defmethod parse :default
  [[op & args :as form] env]
  (let [env (assoc env :context :expr)]
    {:op 'invoke
     :form form
     :env env
     :fn (analyze op env)
     :args (mapv (analyze-in env) args)}))

(defn analyze-const [form env]
  (let [env (assoc env :context :expr)]
    {:op 'const
     :form form
     :env env}))

(defn analyze-vector [form env]
  (let [env (assoc env :context :expr)]
    {:op 'vector
     :form form
     :env env
     :items (mapv (analyze-in env) form)}))

(defn analyze-map [form env]
  (let [env (assoc env :context :expr)]
    {:op 'map
     :form form
     :env env
     :keys (mapv (analyze-in env) (keys form))
     :vals (mapv (analyze-in env) (vals form))}))

(defn analyze-set [form env]
  (let [env (assoc env :context :expr)]
    {:op 'set
     :form form
     :env env
     :items (mapv (analyze-in env) form)}))

(defn analyze-symbol [form env]
  (let [env (assoc env :context :expr)
        base {:form form :env env}
        error #(throw (Exception. (str % ": " form)))]
    (if-let [index (find-index env form)]
      (assoc base :op 'local :index index)
      (let [obj (get (:vars env) form ::not-found)]
        (cond (= obj ::not-found) (error "Unable to resolve symbol")
              (:macro? (meta obj)) (error "Can't take the value of a macro")
              :else (assoc base :op 'var :obj obj))))))

(defn empty-env [& opts]
  (merge
   {:vars {}
    :locals []
    :context :toplevel
    :expand (fn [& args]
              (throw (Exception. "No macroexpansion function provided")))}
   opts))

(defn analyze-in [env]
  (fn [form] (analyze form env)))

(defn analyze
  [form {:keys [expand] :as env}]
  (letfn [(call? [form]
            (and (seq? form) (seq form)))
          (var? [form]
            (and (symbol? form)
                 (not (special-operator? form))
                 (not (has-local? env form))
                 (has-var? env form)))]
    (cond (symbol? form)   (analyze-symbol form env)
          (constant? form) (analyze-const form env)
          (vector? form)   (analyze-vector form env)
          (map? form)      (analyze-map form env)
          (set? form)      (analyze-set form env)
          (call? form)     (let [[op & args] (seq form)]
                             (if (var? op)
                               (let [exp (expand form)]
                                 (if (identical? form exp)
                                   (parse form env)
                                   (recur exp env)))
                               (parse form env)))
          :else (throw (Exception. (str "Unsupported form: " form))))))

(defn show [m]
  (reduce-kv (fn [result k v]
               (assoc result
                 k (cond (= k :env) 'ELIDED
                         (map? v)   (show v)
                         :else      v)))
             {}
             m))
