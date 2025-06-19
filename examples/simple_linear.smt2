;; 简单线性算术问题示例
;; 求解二维线性规划问题

(set-logic QF_LIA)
(set-info :source |OptiSMT Example: Simple Linear Programming|)

;; 声明变量
(declare-fun x () Int)
(declare-fun y () Int)

;; 约束条件
(assert (>= x 0))          ; x >= 0
(assert (>= y 0))          ; y >= 0
(assert (<= (+ x y) 10))   ; x + y <= 10
(assert (>= (+ (* 2 x) y) 5))  ; 2x + y >= 5

;; 目标函数：最大化 x + y
(maximize (+ x y))

;; 检查可满足性
(check-sat)
(get-model) 