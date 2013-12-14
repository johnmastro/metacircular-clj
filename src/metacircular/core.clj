(ns metacircular.core
  (:refer-clojure :exclude [eval apply load-file])
  (:require [clojure.core :as clj]
            [clojure.java.io :as io]
            [clojure.walk :as walk]
            [metacircular.env :as env]
            [metacircular.analyzer :refer [analyze special-form?]])
  (:import  (java.io Writer FileReader PushbackReader)))

;; -----------------------------------------------------------------------------
;; Procedures (primitives, closures, and macros)
;; -----------------------------------------------------------------------------

(defn import-primitives [m]
  (into {} (for [[ns syms] (seq m), sym syms]
             [sym @(ns-resolve ns sym)])))

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

(defn valid-args?
  "Return true if op can be applied to args."
  [op args]
  (let [{:keys [min-args max-args]} (.arg-spec op)]
    (<= min-args (count args) max-args)))

(defn make-formals
  "Return a map of formals based on op and args."
  [op args]
  (when-not (valid-args? op args)
    (let [meta (meta op)
          name (or (:name meta)
                   (if (:macro? meta)
                     "macro"
                     "procedure"))]
      (throw (Exception. (str "Wrong number of args for " name)))))
  (let [{:keys [positionals variadic]} (.arg-spec op)]
    (if variadic
      (let [[p-args v-args] (split-at (count positionals) args)]
        (-> (zipmap positionals p-args)
            (assoc variadic (seq v-args))))
      (zipmap positionals args))))

(deftype Procedure [arg-spec body env metadata]
  clojure.lang.IObj
  (meta [_] metadata)
  (withMeta [_ m] (Procedure. arg-spec body env m)))

(defn make-procedure [arg-spec body env]
  (Procedure. arg-spec body env {}))

(defmethod print-method Procedure [o ^Writer w]
  (.write w "#<")
  (.write w (.getName (class o)))
  (.write w ": ")
  (if-let [name (-> o meta :name)]
    (.write w (str name))
    (.write w "[anonymous]"))
  (.write w ">"))

(declare exec)

(defn -apply
  "Implementation of apply for Procedure."
  ;; Also inlined in exec to achieve tail call elimination
  ([op args]
     (let [formals (make-formals op args)
           env (env/extend (.env op)
                 ;; TODO: Is there a better way to give the closure
                 ;; a reference to itself?
                 (merge (when-let [name (-> op meta :name)]
                          {name op})
                        formals))]
       (when-let [body (seq (.body op))]
         (doseq [e (butlast body)]
           (exec e env))
         (exec (last body) env))))
  ([op a args] (-apply op (cons a args)))
  ([op a b args] (-apply op (list* a b args)))
  ([op a b c args] (-apply op (list* a b c args))))

(defn procedure?
  "Return true is a Procedure."
  [x]
  (instance? Procedure x))

(defn apply
  ([op args]
     (if (procedure? op)
       (-apply op args)
       (clj/apply op args)))
  ([op a args] (cons a args))
  ([op a b args] (list* a b args))
  ([op a b c args] (list* a b c args)))

(defn invokable?
  "Return true if x is a Procedure or implements IFn."
  [x]
  (or (ifn? x) (procedure? x)))

(defn macro?
  "Return true if x is a Procedure with :macro? metadata."
  [x]
  (and (instance? Procedure x)
       (boolean (-> x meta :macro?))))

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
  ([vars]
     (env/make-env
      (reduce (fn [result sym]
                (let [f @(ns-resolve 'metacircular.core sym)]
                  (assoc result sym f)))
              vars
              '[apply invokable? error]))))

(declare eval)

(defn expand1
  "Expand expr once and return the result. "
  ([expr] (expand1 expr (make-env)))
  ([expr env]
     (let [[_ obj] (env/find env (first expr))]
       (if (macro? obj)
         (apply obj (rest expr))
         expr))))

(defn expand
  "Fully expand expr (by calling expand1 repeatedly) and return the result. "
  ([expr] (expand expr (make-env)))
  ([expr env]
     (let [expanded (expand1 expr env)]
       (if (identical? expanded expr)
         expanded
         (recur expanded env)))))

(defn expand-all
  "Recursively perform all possible macroexpansions in form."
  ([form] (expand-all form (make-env)))
  ([form env] (walk/prewalk (fn [x] (if (seq? x) (expand x env) x))
                            form)))

(defn analyzer-env [env & opts]
  (merge
   {:vars @(.vars env)
    :locals []
    :context :toplevel
    :expand #(expand1 % env)}
   opts))

(defn exec-in
  "Return a function which will exec AST nodes in env."
  [env]
  (fn [node] (exec node env)))

(defn exec
  "Execute node, an AST node produced by metacircular.analyzer/analyze."
  ([node]
     (exec node (make-env)))
  ([node env]
     (case (:op node)
       const (:form node)
       var (:obj node)
       local (let [{:keys [index form]} node]
               (env/find-local env index form))
       quote (:expr node)
       if (let [{:keys [test then else]} node]
            (if (exec test env)
              (recur then env)
              (recur else env)))
       fn (let [{:keys [name arg-spec body]} node]
            (with-meta (make-procedure arg-spec body env)
              {:name name}))
       defmacro (let [{:keys [target name arg-spec body]} node
                      val (with-meta (make-procedure arg-spec body env)
                            {:name name
                             :macro? true})]
                  (env/def! env target val)
                  val)
       def (let [{:keys [target expr]} node
                 val (exec expr env)]
             (env/def! env target val)
             val)
       set! (let [{:keys [target expr]} node
                  val (exec expr env)]
              (env/set! env target val)
              val)
       invoke (let [{:keys [fn args]} node
                    op (exec fn env)]
                (cond (macro? op)
                      (recur (apply op args) env)

                      (procedure? op)
                      (let [formals (make-formals op (map (exec-in env) args))
                            env (env/extend (.env op)
                                  (merge (when-let [name (-> op meta :name)]
                                           {name op})
                                         formals))]
                        (when-let [body (seq (.body op))]
                          (doseq [e (butlast body)]
                            (exec e env))
                          (recur (last body) env)))

                      (ifn? op)
                      (clj/apply op (map (exec-in env) args))

                      :else
                      (throw (Exception. (str "Not a valid procedure: " op)))))
       vector (into [] (map (exec-in env) (:items node)))
       set (into #{} (map (exec-in env) (:items node)))
       map (zipmap (map (exec-in env) (:keys node))
                   (map (exec-in env) (:vals node)))
       (throw (Exception. (str "Can't exec " node))))))

(defn eval-in
  "Return a function which will eval forms in env."
  [env]
  (fn [form] (eval form env)))

(defn eval
  "Evaluate form the return the result."
  ([form] (eval form (make-env)))
  ([form env]
     (let [a-env (analyzer-env env)]
       (-> form
           (analyze a-env)
           (exec env)))))

(defmacro run
  "Evaluate each expression in body and return the last expression's result.
  This is equivalent to wrapping exprs in a do form and using eval."
  [& body]
  `(let [env# (make-env)
         exprs# '~body]
     (doseq [expr# (butlast exprs#)]
       (eval expr# env#))
     (eval (last exprs#) env#)))

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
  ([file] (load-file file (make-env)))
  ([file env]
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
  ([_] (swap! +core-env+ (fn [& _] (load-file core-file)))))

(defn repl
  ([] (repl (core-env)))
  ([env]
     (let [exit? (comp boolean #{:exit :quit})
           forms (take-while (complement exit?) (repeatedly read))]
       (doseq [form forms]
         (prn (eval form env))))))
