(ns metacircular.core
  (:refer-clojure :exclude [eval apply load-file destructure])
  (:require [clojure.core :as clj]
            [clojure.java.io :as io]
            [clojure.walk :as walk]
            [metacircular.env :as env]
            [metacircular.analyzer :as ana :refer [analyze analyze-arg-list]])
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

(defn make-procedure
  "Create and return a procedure object from an AST node.
  With a :macro keyword argument the procedure will be a macro, otherwise a
  normal function."
  [node env & {macro? :macro}]
  (let [name (:name node)
        make-method #(with-meta (assoc %
                                  :env env
                                  :name name
                                  :procedure (atom nil))
                       {:type ::method})
        methods (reduce-kv (fn [result arity node]
                             (assoc result arity (make-method node)))
                           {}
                           (:methods node))
        procedure (with-meta (merge (select-keys node [:name :arities])
                                    {:macro? macro?
                                     :methods methods})
                    {:type ::procedure})]
    ;; This seems like a bit of a kludge but each method should have a link to
    ;; the procedure it belongs to and I haven't come up with a better way to
    ;; do that.
    (doseq [entry (:methods procedure)]
      (reset! (-> entry val :procedure) procedure))
    procedure))

(defn find-method
  "Return the appropriate method (arity) of f for args.
  Throw an exception if there is no matching method."
  [f args]
  (let [count (count args)]
    (if-let [fixed (get (:methods f) count)]
      fixed
      (let [variadic (-> f :methods :variadic)]
        (if (and variadic
                 (>= count (:positionals variadic)))
          variadic
          (let [name (:name f)
                desc (or name (if (:macro? f)
                                "macro"
                                "procedure"))]
            (throw (ex-info (str "Wrong number of args for " desc)
                            {:procedure f :args args}))))))))

(declare exec push-bindings)

(defn -apply
  "Implementation of apply for Procedure."
  ;; Also inlined in exec to achieve tail call elimination
  ([op args]
     (let [method (find-method op args)
           env (push-bindings method args)]
       (doseq [e (:statements method)]
         (exec e env))
       (exec (:return method) env)))
  ([op a args] (-apply op (cons a args)))
  ([op a b args] (-apply op (list* a b args)))
  ([op a b c args] (-apply op (list* a b c args))))

(defn procedure?
  "Return true if x is a procedure map."
  [x]
  (= (type x) ::procedure))

(defn apply
  "Apply op to args."
  ([op args]
     (if (procedure? op)
       (-apply op args)
       (clj/apply op args)))
  ([op a args] (cons a args))
  ([op a b args] (list* a b args))
  ([op a b c args] (list* a b c args)))

(defn invokable?
  "Return true if x is a procedure or implements IFn."
  [x]
  (or (ifn? x) (procedure? x)))

(defn macro?
  "Return true if x is a procedure which is a macro."
  [x]
  (and (procedure? x) (:macro? x)))

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
  ([expr] (expand1 expr @default-env))
  ([expr env]
     (let [[_ obj] (env/find env (first expr))]
       (if (macro? obj)
         (apply obj (rest expr))
         expr))))

(defn expand
  "Fully expand expr (by calling expand1 repeatedly) and return the result. "
  ([expr] (expand expr @default-env))
  ([expr env]
     (let [expanded (expand1 expr env)]
       (if (identical? expanded expr)
         expanded
         (recur expanded env)))))

(defn expand-all
  "Recursively perform all possible macroexpansions in form."
  ([form] (expand-all form @default-env))
  ([form env] (walk/prewalk (fn [x] (if (seq? x) (expand x env) x))
                            form)))

(defn analyzer-env
  "Return an appropriate analyzer environment based on env (an evaluation
  environment) and opts (a map)."
  [env & opts]
  (merge (ana/make-env)
         {:vars @(:vars env)
          :locals []
          :context :toplevel
          :expand #(expand1 % env)}
         opts))

(defn exec-in
  "Return a function which will exec AST nodes in env."
  [env]
  (fn [node] (exec node env)))

(defn destructure
  "Destructure vals as per arg-list.
  arg-list must be an AST node as returned by analyze-arg-list."
  [arg-list vals]
  (letfn [(process-bind [result node v]
            (case (:type node)
              symbol (assoc result (:form node) v)
              vector (process-vec result node v)
              map (process-map result node v)
              (throw (ex-info "Malformed binding node"
                              {:node node :val v}))))
          (process-vec [result node vs]
            (loop [result result, items (:items node), n 0]
              (if-let [[item & more] (seq items)]
                (recur (process-bind result item (nth vs n nil))
                       more
                       (inc n))
                (let [{:keys [rest name]} node]
                  (cond-> result
                    name (process-bind name vs)
                    rest (process-bind rest (nthnext vs n)))))))
          (process-map [result node vs]
            (let [vs (if (seq? vs)
                       (clojure.lang.PersistentHashMap/create (seq vs))
                       vs)]
              (loop [result result, items (:items node)]
                (if-let [[[sym key default] & more] (seq items)]
                  (recur (process-bind result sym (get vs key default))
                         more)
                  (if-let [name (:name node)]
                    (assoc result name vs)
                    result)))))]
    (process-bind {} arg-list vals)))

(defn push-bindings
  "Return op's env extended with bindings for vals."
  [method vals]
  (let [{:keys [procedure name]} method]
    (env/extend (:env method)
      (let [result (destructure (:arg-list method) vals)]
        (if (and name (not (contains? result name)))
          (assoc result name @procedure)
          result)))))

(defn exec
  "Execute node, an AST node produced by metacircular.analyzer/analyze."
  ([node]
     (exec node @default-env))
  ([node env]
     (case (:op node)
       const (:form node)
       quote (:expr node)
       var (:obj node)
       local (let [{:keys [index form]} node]
               (env/find-local env index form))
       if (let [{:keys [test then else]} node]
            (if (exec test env)
              (recur then env)
              (recur else env)))
       fn (make-procedure node env)
       defmacro (let [val (make-procedure node env :macro true)
                      target (:target node)]
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
                      (let [method (find-method op args)
                            args (map (exec-in env) args)
                            env (push-bindings method args)]
                        (doseq [e (:statements method)]
                          (exec e env))
                        (recur (:return method) env))

                      (ifn? op)
                      (clj/apply op (map (exec-in env) args))

                      :else
                      (throw (ex-info "Not a valid procedure"
                                      {:node node :env env}))))
       vector (->> (:items node)
                (map (exec-in env))
                (into []))
       set (->> (:items node)
             (map (exec-in env))
             (into #{}))
       map (zipmap (map (exec-in env) (:keys node))
                   (map (exec-in env) (:vals node)))
       (throw (ex-info "Invalid AST node" {:node node :env env})))))

(defmacro run
  "Evaluate each expression in body and return the last expression's result.
  This is equivalent to wrapping exprs in a do form and using eval."
  [& body]
  `(let [env# @default-env
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
  ([file] (load-file file @default-env))
  ([file env]
     (doseq [form (read-file file)]
       (eval form env))
     env))

(def core-env (atom nil))

(defn load-core-env
  "Use load-file to load core.mclj. Return the resulting env."
  []
  (let [core-file (io/file (.getPath (io/resource "core.mclj")))]
    (load-file core-file)))

(defn load-core-env!
  "Load the core env and make it the default-env.
  If reload? then do so unconditionally; otherwise, only do so if the
  default-env is currently nil."
  ([] (load-core-env! nil))
  ([reload?]
     (when (or (not @core-env)
               reload?)
       (let [env (load-core-env)]
         (reset! core-env env)
         (reset! default-env env)))))

(defn -eval
  ([form] (-eval form @default-env))
  ([form env]
     (let [a-env (analyzer-env env)]
       (-> form
         (analyze a-env)
         (exec env)))))

(defn eval
  "Evaluate form and return the result."
  ([form]
     (load-core-env!)
     (eval form @default-env))
  ([form env]
     (try (-eval form env)
          (catch Exception exc
            (if (instance? clojure.lang.ExceptionInfo exc)
              (throw exc)
              (throw
               (ex-info "Evaluation error" {:form form :env env :exc exc})))))))

(defn eval-in
  "Return a function which will eval forms in env."
  [env]
  (fn [form] (eval form env)))

(defn read1
  "Print a prompt and read a form."
  ([] (read1 "* "))
  ([prompt]
     (doto *out*
       (.write prompt)
       (.flush))
     (read)))

(defn repl
  "Start a read-eval-print loop.
  Entering either :exit or :quit by itself terminates the REPL."
  ([] (repl @default-env))
  ([env]
     (let [exit? (comp boolean #{:exit :quit})
           forms (take-while (complement exit?) (repeatedly read1))]
       (doseq [form forms]
         (try (prn (eval form env))
              (catch Exception exc
                (println "Error:" (.getMessage exc))))))))

(def banner "metacircular-clj REPL (enter :exit to leave)")

(defn print-banner []
  (println banner)
  (println (apply str (repeat (count banner) "-")))
  (newline))

(defn -main [& _]
  (load-core-env!)
  (print-banner)
  (repl))
