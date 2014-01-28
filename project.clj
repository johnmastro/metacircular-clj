(defproject metacircular "0.1.0-SNAPSHOT"
  :description "A simple metacircular interpreter in Clojure."
  :url "https://github.com/johnmastro/metacircular-clj"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.5.1"]]
  :target-path "target/%s"
  :profiles {:dev {:dependencies [[org.clojure/tools.namespace "0.2.4"]]
                   :source-paths ["dev"]}}
  :main metacircular.core)
