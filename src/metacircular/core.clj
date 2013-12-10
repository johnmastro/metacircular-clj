(ns metacircular.core
  (:refer-clojure :exclude [eval apply load-file])
  (:require [clojure.core :as clj]
            [clojure.java.io :as io]
            [metacircular.env :as env]
            [metacircular.analyzer :refer [analyze special-form?]])
  (:import  (java.io Writer FileReader PushbackReader)))

;; -----------------------------------------------------------------------------
;; Procedures (primitives, closures, and macros)
;; -----------------------------------------------------------------------------

(defprotocol IProcedure
  (apply
    [proc args]
    [proc a args]
    [proc a b args]
    [proc a b c args]))

(deftype Primitive [name function]
  IProcedure
  (apply [this args] (clj/apply function args))
  (apply [this a args] (clj/apply function a args))
  (apply [this a b args] (clj/apply function a b args))
  (apply [this a b c args] (clj/apply function a b c args)))

(defn import-primitives [m]
  (into {} (for [[ns syms] (seq m), sym syms]
             [sym (Primitive. sym @(ns-resolve ns sym))])))

(def primitives
  (import-primitives
   '{clojure.core   [* + - / < <= = > >= assoc assoc-in char? class compare
                     concat conj cons contains? count dec dissoc double drop
                     drop-last empty? even? false? find first ffirst fnext
                     gensym get get-in hash-map identity inc int interpose
                     interleave into key keyword keyword? last list list* list?
                     map? neg? nfirst next nnext nthnext nthrest nil? not not=
                     nth number? odd? partition partition-all pos? pr-str
                     println prn-str range read-string rem rest repeat reverse
                     second seq seq? set set? split-at str string? symbol
                     symbol? take take-nth true? type update-in val vec vector
                     vector? zero? zipmap]
     clojure.set    [difference index intersection join map-invert project
                     rename rename-keys select subset? superset? union]
     clojure.string [blank? capitalize escape lower-case split split-lines trim
                     trim-newline triml trimr upper-case]}))

(defn primitive?
  "Return true if x is a Primitive."
  [x]
  (instance? Primitive x))

(defmethod print-method Primitive [o ^Writer w]
  (.write w "#<")
  (.write w (.getName (class o)))
  (.write w ": ")
  (.write w (str (.name o)))
  (.write w ">"))

(defn valid-args?
  "Return true if a procedure with arg-spec can be applied to args."
  [arg-spec args]
  (let [{:keys [min-args max-args]} arg-spec]
    (<= min-args (count args) max-args)))

(defn make-formals
  "Return a map of formals based on op and args."
  [op args]
  (let [{:keys [positionals variadic] :as arg-spec} (.arg-spec op)]
    (when-not (valid-args? arg-spec args)
      (let [name (or (.name op) "closure")]
        (throw (Exception. (str "Wrong number of args for " name)))))
    (if variadic
      (let [[p-args v-args] (split-at (count positionals) args)]
        (-> (zipmap positionals p-args)
            (assoc variadic (seq v-args))))
      (zipmap positionals args))))

(declare eval)

(defn -apply
  "Implementation of apply shared by Closure and Macro."
  ;; Apply for Closure is also inlined in eval to achieve tail call elimination
  ([this args]
     (let [formals (make-formals this args)
           env (env/extend (.env this)
                 ;; TODO: Is there a better way to give the closure
                 ;; a reference to itself?
                 (merge (when-let [name (.name this)]
                          {name this})
                        formals))]
       (when-let [body (seq (.body this))]
         (doseq [e (butlast body)]
           (eval e env))
         (eval (last body) env))))
  ([this a args] (-apply this (cons a args)))
  ([this a b args] (-apply this (list* a b args)))
  ([this a b c args] (-apply this (list* a b c args))))

(deftype Closure [name arg-spec body env])

(extend Closure
  IProcedure
  {:apply -apply})

(defn closure?
  "Return true if x is a Closure."
  [x]
  (instance? Closure x))

(defmethod print-method Closure [o ^Writer w]
  (.write w "#<")
  (.write w (.getName (class o)))
  (.write w ": ")
  (if-let [name (.name o)]
    (.write w (str name))
    (.write w "[anonymous]"))
  (.write w ">"))

(deftype Macro [name arg-spec body env])

(extend Macro
  IProcedure
  {:apply -apply})

(defn macro?
  "Return true if x is a Macro."
  [x]
  (instance? Macro x))

(defn procedure?
  "Return true is x's class extends IProcedure."
  [x]
  (extends? IProcedure (class x)))

;; -----------------------------------------------------------------------------
;; Evaluation
;; -----------------------------------------------------------------------------

(defn error [& args]
  ;; Need a way to signal errors in metacircular code
  (let [message (clj/apply str (interpose " " args))]
    (throw (Exception. message))))

(defn make-env
  "Create and return a new environment."
  ([] (make-env primitives))
  ([globals]
     (env/make-env
      (reduce (fn [result sym]
                (let [f @(ns-resolve 'metacircular.core sym)]
                  (assoc result sym (Primitive. sym f))))
              globals
              '[apply primitive? closure? macro? procedure? error]))))

(defn make-simple-env
  "Create and return a new simple environment."
  ([] (make-simple-env primitives))
  ([globals]
     (env/make-simple-env
      (reduce (fn [result sym]
                (let [f @(ns-resolve 'metacircular.core sym)]
                  (assoc result sym (Primitive. sym f))))
              globals
              '[apply primitive? closure? macro? procedure? error]))))

(defn push-bindings [env bindings]
  (reduce (fn [env [sym e]]
            (env/bind env sym (eval e env)))
          env
          (partition 2 bindings)))

(defn eval
  "Evaluate expr and return the result."
  ([form]
     (eval form (make-env)))
  ([form env]
     (letfn [(eval* [expr]
               (eval expr env))]
       (let [code (analyze form)]
         (case (:op code)
           const (:form code)
           symbol (env/lookup env (:form code))
           quote (:expr code)
           if (let [{:keys [test then else]} code]
                (if (eval test env)
                  (recur then env)
                  (recur else env)))
           fn (let [{:keys [name arg-spec body]} code]
                (Closure. name arg-spec body env))
           macro (let [{:keys [name arg-spec body]} code]
                   (Macro. name arg-spec body (env/null-locals env)))
           def (let [{:keys [target expr]} code
                     val (eval expr env)]
                 (env/def! env target val)
                 val)
           set! (let [{:keys [target expr]} code
                      val (eval expr env)]
                  (env/set! env target val)
                  val)
           invoke (let [{:keys [fn args]} code
                        op (eval fn env)]
                    (cond (macro? op)
                          (recur (apply op args) env)

                          (closure? op)
                          (let [formals (make-formals op (map eval* args))
                                env (env/extend (.env op)
                                      (merge (when-let [name (.name op)]
                                               {name op})
                                             formals))]
                            (when-let [body (seq (.body op))]
                              (doseq [e (butlast body)]
                                (eval e env))
                              (recur (last body) env)))

                          (primitive? op)
                          (apply op (map eval* args))

                          (ifn? op)
                          (clj/apply op (map eval* args))

                          :else
                          (throw (Exception.
                                  (str "Not a valid procedure: " op)))))
           vector (into [] (map eval* form))
           set (into #{} (map eval* form))
           map (zipmap (map eval* (keys form)) (map eval* (vals form)))
           (throw (Exception. (str "Can't eval " form))))))))

(defn expand1
  "Expand expr once and return the result. See also expand."
  ([expr] (expand1 expr (make-env)))
  ([expr env]
     (if (and (seq? expr)
              (not (special-form? expr)))
       (let [op (eval (first expr) env)]
         (if (macro? op)
           (apply op (rest expr))
           expr))
       expr)))

(defn expand
  "Fully expand expr (by calling expand1 repeatedly) and return the result."
  ([expr] (expand expr (make-env)))
  ([expr env]
     (let [expanded (expand1 expr env)]
       (if (identical? expanded expr)
         expanded
         (recur expanded env)))))

(defmacro run
  "Evaluate each expression in body and return the last expression's result.
  This is equivalent to wrapping exprs in a do form and using eval."
  [& body]
  `(eval (list (list* 'fn [] body)) (make-env)))

(defmacro defenv
  "Run body, saving the resulting env to a var named name."
  [name & body]
  `(def ~name
     (let [result# (make-env)]
       (eval (list (list* 'fn [] body)) result#)
       result#)))

(defn read-all
  "Read all objects from rdr and return a seq."
  [rdr]
  (let [eof (Object.)]
    (take-while #(not= % eof) (repeatedly #(read rdr false eof)))))

(defn read-file
  "Return all objects in file and return a seq."
  [file]
  (with-open [rdr (-> file FileReader. PushbackReader.)]
    (doall (read-all rdr))))

(defn load-file
  "Read and evaluate all forms in file. Return the resulting env."
  [file]
  (let [env (make-env)]
    (doseq [form (read-file file)]
      (eval form env))
    env))

(def core-file
  (io/file (.getPath (io/resource "core.mclj"))))

(def +core-env+ (atom (load-file core-file)))

(defn core-env
  "Return the \"core\" environment. With an argument (any argument), reload
  the environment."
  ([] (deref +core-env+))
  ([_] (swap! +core-env+ (constantly #(load-file core-file)))))


