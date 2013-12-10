(ns metacircular.analyzer)

(def special-operators
  '#{def fn if macro set!})

(defn special-operator? [x]
  (contains? special-operators x))

(defn special-form? [form]
  (and (seq? form)
       (contains? special-operators (first form))))

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

(defmulti parse
  (fn [[op & more]] op))

(defmethod parse 'if
  [[op test then else :as form]]
  {:pre [(= (count form) 4)]}
  {:op 'if
   :form form
   :test test
   :then then
   :else else})

(defn valid-definition?
  [form]
  (let [[name arg-list] (if (symbol? (nth form 1))
                          [(nth form 1) (nth form 2)]
                          [nil (nth form 1)])]
    (and (vector? arg-list)
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
  [form]
  (let [[name arg-list body] (if (symbol? (nth form 1)) ; named
                               [(nth form 1) (nth form 2) (drop 3 form)]
                               [nil (nth form 1) (drop 2 form)])
        arg-spec (parse-arg-list arg-list)]
    (merge
     {:name name
      :form form
      :arg-list arg-list
      :arg-spec arg-spec
      :body body})))

(defmethod parse 'fn
  [[op & more :as form]]
  {:pre [(valid-definition? form)]}
  (assoc (parse-definition form) :op 'fn))

(defmethod parse 'macro
  [[op & more :as form]]
  {:pre [(valid-definition? form)]}
  (assoc (parse-definition form) :op 'macro))

(defmethod parse 'def
  [[op target expr :as form]]
  {:pre [(symbol? target) (= (count form) 3)]}
  {:op 'def
   :form form
   :target target
   :expr expr})

(defmethod parse 'set!
  [[op target expr :as form]]
  {:pre [(symbol? target) (= (count form) 3)]}
  {:op 'set!
   :form form
   :target target
   :expr expr})

(defmethod parse 'quote
  [[op expr & _ :as form]]
  {:op 'quote
   :form form
   :expr expr})

(defmethod parse :default
  [[op & args :as form]]
  {:op 'invoke
   :form form
   :fn op
   :args args})

(defn analyze-const [form]
  {:op 'const
   :form form})

(defn analyze-vector [form]
  {:op 'vector
   :form form})

(defn analyze-map [form]
  {:op 'map
   :form form})

(defn analyze-set [form]
  {:op 'set
   :form form})

(defn analyze-symbol [form]
  {:op 'symbol
   :form form})

(defn analyze [form]
  (let [invoke? #(and (seq? %) (seq %))]
    (cond (symbol? form)    (analyze-symbol form)
          (constant? form)  (analyze-const form)
          (vector? form)    (analyze-vector form)
          (map? form)       (analyze-map form)
          (set? form)       (analyze-set form)
          (invoke? form)    (parse form)
          :else (throw (Exception. (str "Unsupported form: " form))))))
