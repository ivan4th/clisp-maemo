;; netica demo
(defpackage "NETICA-DEMO" (:use "CL" "EXT" "FFI" "NETICA"))
(in-package "NETICA-DEMO")

(netica:start-netica "+DunnM/Alphatech/310-2/5865")
(defvar *net* (netica:make-net :name "AsiaEx"))
(defvar *visit-asia*
  (netica:make-node :name "VisitAsia" :net *net*
                    :cpt '((#() . #(0.01f0 0.99f0)))
                    :states '("visit" "no_visit")))
(defvar *tuberculosis*
  (netica:make-node :name "Tuberculosis" :net *net*
                    :parents (list *visit-asia*)
                    :cpt '((#("visit") . #(0.05f0 0.95f0))
                           (#("no_visit") . #(0.01f0 0.99f0)))
                    :states '("present" "absent")))
(defvar *smoking*
  (netica:make-node :name "Smoking" :net *net*
                    :cpt '((#() . #(0.5f0 0.5f0)))
                    :states '("smoker" "nonsmoker")))
(defvar *cancer*
  (netica:make-node :name "Cancer" :net *net*
                    :title "Lung Cancer" :parents (list *smoking*)
                    :cpt '((#("smoker") . #(0.1f0 0.9f0))
                           (#("nonsmoker") . #(0.01f0 0.99f0)))
                    :states '("present" "absent")))
(defvar *tb-or-ca*
  (netica:make-node :name "TbOrCa" :net *net*
                    :title "Tuberculosis or Cancer"
                    :parents (list *tuberculosis* *cancer*)
                    :cpt '((#("present" "present") . #(1f0 0f0))
                           (#("present" "absent") . #(1f0 0f0))
                           (#("absent" "present") . #(1f0 0f0))
                           (#("absent" "absent") .  #(0f0 1f0)))
                    :states '("true" "false")))
(defvar *xray*
  (netica:make-node :name "XRay" :net *net*
                    :parents (list *tb-or-ca*)
                    :cpt '((#("true") . #(0.98f0 0.02f0))
                           (#("false") . #(0.05f0 0.95f0)))
                    :states '("abnormal" "normal")))

(netica:CompileNet_bn *net*)
(netica:check-errors)

(netica:get-beliefs *tuberculosis* :verbose t)

(netica:enter-finding *net* "XRay" "abnormal")
(format t "~&Given an abnormal X-ray:~%")
(netica:get-beliefs *tuberculosis* :verbose t)

(netica:enter-finding *net* "VisitAsia" "visit")
(format t "~&Given an abnormal X-ray and a visit to Asia:~%")
(netica:get-beliefs *tuberculosis* :verbose t)

(netica:enter-finding *net* "Cancer" "present")
(format t "~&Given abnormal X-ray, Asia visit, and lung cancer:~%")
(netica:get-beliefs *tuberculosis* :verbose t)

(netica:save-net "asia" *net*)

;; termination
(netica:delete-net_bn *net*)
(close-netica)
