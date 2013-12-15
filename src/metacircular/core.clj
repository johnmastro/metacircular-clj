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

(deftype Procedure [arg-spec statements return env metadata]
  clojure.lang.IObj
  (meta [_] metadata)
  (withMeta [_ m] (Procedure. arg-spec statements return env m)))

(defn make-procedure [arg-spec body env]
  (let [{:keys [statements return]} body]
    (Procedure. arg-spec statements return env {})))

(defmethod print-method Procedure [o ^Writer w]
  (.write w "#<")
  (.write w (.getName (class o)))
  (.write w ": ")
  (if-let [name (-> o meta :name)]
    (.write w (str name))
    (.write w "[anonymous]"))
  (.write w ">"))

(declare exec push-bindings!)

(defn -apply
  "Implementation of apply for Procedure."
  ;; Also inlined in exec to achieve tail call elimination
  ([op args]
     (let [env (push-bindings! op args)]
       (doseq [e (.statements op)]
         (exec e env))
       (exec (.return op) env)))
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

(def default-env (atom (make-env)))

(declare eval)

(defn expand1
  "Expand expr once and return the result. "
  ([expr] (expand1 expr (env/copy @default-env)))
  ([expr env]
     (let [[_ obj] (env/find env (first expr))]
       (if (macro? obj)
         (apply obj (rest expr))
         expr))))

(defn expand
  "Fully expand expr (by calling expand1 repeatedly) and return the result. "
  ([expr] (expand expr (env/copy @default-env)))
  ([expr env]
     (let [expanded (expand1 expr env)]
       (if (identical? expanded expr)
         expanded
         (recur expanded env)))))

(defn expand-all
  "Recursively perform all possible macroexpansions in form."
  ([form] (expand-all form (env/copy @default-env)))
  ([form env] (walk/prewalk (fn [x] (if (seq? x) (expand x env) x))
                            form)))

(defn analyzer-env [env & opts]
  (merge
   {:vars @(:vars env)
    :locals []
    :context :toplevel
    :expand #(expand1 % env)}
   opts))

(defn exec-in
  "Return a function which will exec AST nodes in env."
  [env]
  (fn [node] (exec node env)))

(defn push-bindings! [op vals]
  (when-not (valid-args? op vals)
    (let [meta (meta op)
          name (or (:name meta)
                   (if (:macro? meta)
                     "macro"
                     "procedure"))]
      (throw (Exception. (str "Wrong number of args for " name)))))
  (let [frame (if-let [name (-> op meta :name)]
                (atom {name op})
                (atom {}))
        env (env/extend* (.env op) frame)
        arg-list (-> op .arg-spec :arg-list)]
    (letfn [(process-bind [b v]
              (cond (symbol? b) (swap! frame assoc b v)
                    (vector? b) (process-vec b v)
                    (map? b) (process-map b v)
                    :else
                    (throw (Exception. (str "Unsupported binding form: " b)))))
            (process-vec [bs vs]
              (loop [bs bs, n 0, seen-rest? false]
                (when-let [[b1 b2 & more] (seq bs)]
                  (cond (= b1 '&) (do (process-bind b2 (nthnext vs n))
                                      (recur more n true))
                        (= b1 :as) (process-bind b2 vs)
                        :else (if seen-rest?
                                (throw (Exception. "Unsupported binding form"))
                                (do (process-bind b1 (nth vs n nil))
                                    (recur (next bs) (inc n) seen-rest?)))))))
            (process-map [bs vs]
              (let [vs (if (seq? vs)
                         (clojure.lang.PersistentHashMap/create (seq vs))
                         vs)
                    defaults (:or bs)
                    as-name (:as bs)
                    keys-vec (:keys bs)]
                (when as-name
                  (process-bind as-name vs))
                (doseq [key keys-vec]
                  (let [default (get defaults key nil)]
                    (process-bind key (get vs (keyword key) default))))
                (loop [bs (seq (dissoc bs :as :or :keys))]
                  (when-let [[[key val] & more] bs]
                    (let [default (get defaults key nil)]
                      (process-bind key (get vs val default))
                      (recur (next bs)))))))]
      (process-bind arg-list vals)
      env)))

(defn exec
  "Execute node, an AST node produced by metacircular.analyzer/analyze."
  ([node]
     (exec node (env/copy @default-env)))
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
                      (let [env (push-bindings! op (map (exec-in env) args))]
                        (doseq [e (.statements op)]
                          (exec e env))
                        (recur (.return op) env))

                      (ifn? op)
                      (clj/apply op (map (exec-in env) args))

                      :else
                      (throw (Exception. (str "Not a valid procedure: " op)))))
       vector (into [] (map (exec-in env) (:items node)))
       set (into #{} (map (exec-in env) (:items node)))
       map (zipmap (map (exec-in env) (:keys node))
                   (map (exec-in env) (:vals node)))
       (throw (Exception. (str "Can't exec " node))))))

(defmacro run
  "Evaluate each expression in body and return the last expression's result.
  This is equivalent to wrapping exprs in a do form and using eval."
  [& body]
  `(let [env# (env/copy @default-env)
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
  ([file] (load-file file (env/copy @default-env)))
  ([file env]
     (doseq [form (read-file file)]
       (eval form env))
     env))

(def core-env (atom nil))

(defn load-core-env []
  (let [core-file (io/file (.getPath (io/resource "core.mclj")))]
    (load-file core-file)))

(defn load-core-env!
  ([] (load-core-env! nil))
  ([reload] (when (or (not @core-env)
                      reload)
              (let [env (load-core-env)]
                (reset! core-env env)
                (reset! default-env env)))))

(defn -eval
  ([form] (-eval form (env/copy @default-env)))
  ([form env]
     (let [a-env (analyzer-env env)]
       (-> form
           (analyze a-env)
           (exec env)))))

(defn eval
  "Evaluate form the return the result."
  ([form]
     (load-core-env!)
     (eval form (env/copy @default-env)))
  ([form env]
     (-eval form env)))

(defn eval-in
  "Return a function which will eval forms in env."
  [env]
  (fn [form] (eval form env)))

(defn repl
  ([] (repl (env/copy @default-env)))
  ([env]
     (let [exit? (comp boolean #{:exit :quit})
           forms (take-while (complement exit?) (repeatedly read))]
       (doseq [form forms]
         (prn (eval form env))))))
