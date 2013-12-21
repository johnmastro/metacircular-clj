(ns metacircular.analyzer
  (:require [clojure.walk :as walk]))

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
  {:pre [(or (= (count form) 3)
             (= (count form) 4))]}
  (let [env (assoc env :context :expr)]
    {:op 'if
     :form form
     :env env
     :test (analyze test env)
     :then (analyze then env)
     :else (analyze else env)}))

(defn valid-fn-form?
  [form]
  (let [[op one two three] form]
    (and (= op 'fn)
         (or (vector? one)                                 ;; (fn [] ...)
             (and (symbol? one) (vector? two))             ;; (fn name [] ...)
             (and (seq? one) (vector? (first one)))        ;; (fn ([] ...))
             (and (symbol? one) (vector? (first two))))))) ;; (fn name ([] ...))

(defn analyze-arg-list [arg-list]
  (letfn [(error [form]
            (throw (Exception. (str "Unsupported binding form: " form))))
          (analyze-bind [form]
            (cond (symbol? form) (analyze-sym form)
                  (vector? form) (analyze-vec form)
                  (map? form) (analyze-map form)
                  :else (error form)))
          (analyze-sym [form]
            {:type 'symbol :form form})
          (analyze-vec [form]
            (let [[pos more] (split-with (complement '#{& :as}) form)
                  analyze-more
                  (fn analyze-more [more]
                    (loop [result {} more more]
                      (if-let [[a b & z] (seq more)]
                        (case a
                          & (if (:rest result)
                              (error more)
                              (recur (assoc result :rest (analyze-bind b))
                                     z))
                          :as (if (seq z)
                                (error z)
                                (assoc result :name (analyze-bind b)))
                          (error more))
                        result)))]
              (merge
               {:type 'vector
                :form form
                :items (map analyze-bind pos)
                :rest nil
                :name nil}
               (analyze-more more))))
          (analyze-map [form]
            (let [{keys :keys defaults :or} form
                  mappings (into (dissoc form :or :as :keys)
                                 (zipmap keys (map keyword keys)))
                  make-tuple (fn [[sym key]]
                               [(analyze-bind sym)
                                key
                                (get defaults sym nil)])]
              {:type 'map
               :form form
               :items (map make-tuple mappings)
               :name (:as form)}))]
    (if (some #{:as} arg-list)
      ;; Clojure doesn't allow :as at the top level of arglists
      (error ":as")
      {:arg-list (analyze-bind arg-list)
       :positionals (->> arg-list
                      (take-while (complement '#{&}))
                      (count))
       :variadic? (boolean (some '#{&} arg-list))})))

(defn find-arg-syms [arg-list]
  (let [walk (fn walk [arg-list]
               (walk/prewalk (fn [x]
                               (if (coll? x)
                                 (seq (if (and (map? x)
                                               (contains? x :or))
                                        (update-in x [:or] keys)
                                        x))
                                 x))
                             arg-list))]
    (->> (walk arg-list)
      (flatten)
      (filter symbol?)
      (remove '#{&})
      (set))))

(defn parse-methods [name sigs env]
  (letfn [(parse-method [[arg-list & body]]
            (let [arg-spec (analyze-arg-list arg-list)
                  syms (cond-> (find-arg-syms arg-list)
                         name (conj name))
                  env (-> env
                        (assoc :context :expr)
                        (update-in [:locals] conj syms))]
              (assoc arg-spec
                :statements (mapv (analyze-in env) (butlast body))
                :return (analyze (last body) env))))]
    (reduce (fn [result method]
              (let [arity (if (:variadic? method)
                            :variadic
                            (:positionals method))]
                (if (contains? result arity)
                  (throw (Exception.
                          (str "Duplicate fn signature"
                               (when name ": " name))))
                  (assoc result arity method))))
            {}
            (map parse-method sigs))))

(defn parse-definition [form env]
  (let [sigs (next form)
        name (when (symbol? (first sigs))
               (first sigs))
        sigs (if name
               (next sigs)
               sigs)
        sigs (if (vector? (first sigs))
               (list sigs)
               (if (and (seq? (first sigs))
                        (vector? (ffirst sigs)))
                 sigs
                 (Exception.
                  (str "Malformed definition"
                       (when name ": " name)))))]
    (let [method-table (parse-methods name sigs env)
          arities (-> method-table keys set)
          methods (vals method-table)
          variadic (:variadic method-table)
          max-fixed (some->> arities
                      (filter number?)
                      (seq)
                      (reduce max))]
      (when (and variadic
                 max-fixed
                 (< (:positionals variadic) max-fixed))
        (throw (Exception. "Fixed arity fn with more params than variadic fn")))
      {:name name
       :form form
       :arities arities
       :methods method-table})))

(defmethod parse 'fn
  [[op & more :as form] env]
  {:pre [(valid-fn-form? form)]}
  (let [env (assoc env :context :expr)]
    (merge
     {:op 'fn
      :env env}
     (parse-definition form env))))

(defmethod parse 'defmacro
  [[op target & more :as form] env]
  {:pre [(symbol? target)
         (valid-fn-form? (cons 'fn more))
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
              (:macro? obj) (error "Can't take the value of a macro")
              :else (assoc base :op 'var :obj obj))))))

(defn make-env [& opts]
  (with-meta (merge {:vars {}
                     :locals []
                     :context :toplevel
                     :expand identity}
                    opts)
    {:type ::env}))

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

