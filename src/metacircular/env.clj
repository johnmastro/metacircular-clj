(ns metacircular.env
  (:refer-clojure :exclude [extend find contains? find-var])
  (:require [clojure.core :as clj]))

(defn make-env
  ([] (make-env {}))
  ([vars] {:vars (atom vars) :locals []}))

(defn def! [env sym val]
  (swap! (:vars env) assoc sym val)
  env)

(defn search-frames [frames sym]
  (some (fn [frame]
          (let [obj (get @frame sym ::not-found)]
            (when (not= obj ::not-found)
              [frame obj])))
        (rseq frames)))

(defn set! [env sym val]
  (if-let [[frame _] (search-frames (:locals env) sym)]
    (do (swap! frame assoc sym val)
        env)
    (throw (Exception. (str "Can't set an unbound variable: " sym)))))

(defn extend [env m]
  (update-in env [:locals] conj (atom m)))

(defn extend* [env a]
  {:pre [(instance? clojure.lang.Atom a)]}
  (update-in env [:locals] conj a))

(defn find-local
  ([env sym]
     (if-let [[_ obj] (search-frames (:locals env) sym)]
       obj
       (throw (Exception. (str "Unable to resolve symbol: " sym)))))
  ([env n sym]
     (if-let [frame (get (:locals env) n)]
       (let [obj (get @frame sym ::not-found)]
         (if (not= obj ::not-found)
           obj
           (throw (Exception. (str "Unable to resolve symbol: " sym)))))
       (throw (Exception. (str "Invalid locals frame: " n))))))

(defn find-var [env sym]
  (let [result (get @(:vars env) sym ::not-found)]
    (if (not= result ::not-found)
      result
      (throw (Exception. (str "Unable to resolve symbol: " sym))))))

(defn find [env sym]
  (if-let [[_ obj] (search-frames (:locals env) sym)]
    [:local obj]
    (let [var (get @(:vars env) sym ::not-found)]
      (when (not= var ::not-found)
        [:var var]))))

(defn contains? [env sym]
  (not (nil? (find env sym))))

(defn copy [env]
  {:vars (atom @(:vars env))
   :locals (mapv (comp atom deref) (:locals env))})
