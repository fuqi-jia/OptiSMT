;; 非线性算术问题示例
;; 包含二次约束的优化问题

(set-logic QF_NRA)
(set-info :source |OptiSMT Example: Nonlinear Programming|)

;; 声明变量
(declare-fun x () Real)
(declare-fun y () Real)

;; 变量边界
(assert (>= x 0.0))
(assert (>= y 0.0))
(assert (<= x 5.0))
(assert (<= y 5.0))

;; 非线性约束：圆形可行域
;; x^2 + y^2 <= 9 (半径为3的圆)
(assert (<= (+ (* x x) (* y y)) 9.0))

;; 线性约束
(assert (>= (+ x y) 1.0))

;; 二次约束：椭圆约束
;; 2x^2 + y^2 <= 8
(assert (<= (+ (* 2.0 (* x x)) (* y y)) 8.0))

;; 目标函数：最小化二次函数
;; minimize x^2 + y^2 - 2x - 2y
(minimize (+ (* x x) (* y y) (* -2.0 x) (* -2.0 y)))

(check-sat)
(get-model) 