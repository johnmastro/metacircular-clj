(ns metacircular.env
  (:refer-clojure :exclude [extend contains? find-var])
  (:require [clojure.core :as clj]))

(deftype Env [vars locals])

(defn make-env
  ([] (make-env {}))
  ([vars] (Env. (atom vars) [])))

(defn def! [env sym val]
  (swap! (.vars env) assoc sym val)
  env)

(defn set! [env sym val]
  (if-let [frame (loop [locals (.locals env)]
                   (when (seq locals)
                     (let [frame (peek locals)]
                       (if (clj/contains? @frame sym)
                         frame
                         (recur (pop locals))))))]
    (do (swap! frame assoc sym val)
        env)
    (throw (Exception. (str "Can't set an unbound variable: " sym)))))

(defn bind [env sym val]
  (Env. (.vars env) (conj (.locals env) (atom {sym val}))))

(defn extend [env m]
  (Env. (.vars env) (conj (.locals env) (atom m))))

(defn find-local
  ([env sym] (find-local env sym ::throw))
  ([env sym not-found]
     (let [result (loop [locals (.locals env)]
                    (if (seq locals)
                      (let [frame (peek locals)
                            x (get @frame sym ::not-found)]
                        (if (= x ::not-found)
                          (recur (pop locals))
                          x))
                      ::not-found))]
       (if (= result ::not-found)
         (if (= not-found ::throw)
           (throw (Exception. (str "Unable to resolve symbol: " sym)))
           not-found)
         result))))

(defn find-var
  ([env sym] (find-var env sym ::throw))
  ([env sym not-found]
     (let [result (get @(.vars env) sym ::not-found)]
       (if (= result ::not-found)
         (if (= not-found ::throw)
           (throw (Exception. (str "Unable to resolve symbol: " sym)))
           not-found)
         result))))

(defn lookup
  ([env sym] (lookup env sym ::throw))
  ([env sym not-found]
     (let [local (find-local env sym ::not-found)]
       (if (= local ::not-found)
         (let [global (find-var env sym ::not-found)]
           (if (= global ::not-found)
             (if (= not-found ::throw)
               (throw (Exception. (str "Unable to resolve symbol: " sym)))
               not-found)
             global))
         local))))

(defn contains? [env sym]
  (not= (lookup env sym ::not-found)
        ::not-found))

(defn copy [env]
  (Env. (atom @(.vars env)) (mapv (comp atom deref) (.locals env))))
