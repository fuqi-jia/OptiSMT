#pragma once

#include "../theory_solver.h"
#include <unordered_set>

namespace OptiSMT {

    // 非线性算术理论求解器
    class NonlinearArithmeticSolver : public TheorySolver {
    private:
        std::unordered_map<std::string, NodePtr> declared_variables_;
        std::unordered_set<std::string> integer_variables_;
        std::unordered_set<std::string> real_variables_;
        
        // 线性化参数
        double linearization_precision_;
        size_t max_piecewise_segments_;
        
    public:
        NonlinearArithmeticSolver() : linearization_precision_(1e-6), max_piecewise_segments_(100) {}
        ~NonlinearArithmeticSolver() override = default;
        
        // 实现基类接口
        TransformationResult transformConstraint(NodePtr constraint) override;
        TransformationResult transformConstraints(const std::vector<NodePtr>& constraints) override;
        
        // 变量处理
        bool declareVariable(const std::string& name, NodePtr var_node) override;
        std::vector<std::string> getVariables() const override;
        std::string getVariableType(const std::string& name) const override;
        
        // BigM方法支持
        double computeBigM(NodePtr constraint) override;
        bool supportsBigM() const override { return true; }
        
        // 辅助方法
        bool canHandle(NodePtr node) const override;
        std::string getTheoryName() const override { return "NonlinearArithmetic"; }
        void reset() override;
        
        // 预处理
        NodePtr preprocessConstraint(NodePtr constraint) override;
        bool simplifyConstraint(NodePtr& constraint) override;
        
        // 配置方法
        void setLinearizationPrecision(double precision);
        void setMaxPiecewiseSegments(size_t segments);
        
    private:
        // 非线性项转换
        std::string transformNonlinearTerm(NodePtr term);
        std::string transformNonlinearConstraint(NodePtr constraint);
        
        // 乘法项线性化
        std::string linearizeMultiplication(NodePtr mult_node);
        std::string linearizeBilinearTerm(const std::string& var1, const std::string& var2);
        std::string linearizeQuadraticTerm(const std::string& var);
        
        // 超越函数线性化
        std::string linearizeTranscendentalFunction(NodePtr func_node);
        std::string linearizePowerFunction(NodePtr pow_node);
        std::string linearizeExponentialFunction(NodePtr exp_node);
        std::string linearizeLogarithmFunction(NodePtr log_node);
        std::string linearizeTrigonometricFunction(NodePtr trig_node);
        
        // 分段线性逼近
        std::string createPiecewiseLinearApproximation(
            const std::string& input_var, 
            const std::string& output_var,
            std::function<double(double)> func,
            double lower_bound, 
            double upper_bound,
            size_t segments
        );
        
        // SOS2 (Special Ordered Sets of type 2) 约束
        std::string createSOS2Constraints(const std::vector<std::string>& lambda_vars);
        
        // McCormick包络
        std::string createMcCormickEnvelope(
            const std::string& w_var,  // w = x * y
            const std::string& x_var,
            const std::string& y_var,
            double x_lower, double x_upper,
            double y_lower, double y_upper
        );
        
        // 辅助方法
        bool isNonlinearExpression(NodePtr expr) const;
        bool containsMultiplication(NodePtr expr) const;
        bool containsTranscendentalFunction(NodePtr expr) const;
        std::vector<NodePtr> extractMultiplicationTerms(NodePtr expr) const;
        std::pair<double, double> estimateVariableBounds(const std::string& var_name) const;
        
        // 线性化策略选择
        enum class LinearizationStrategy {
            MCCORMICK_ENVELOPE,
            PIECEWISE_LINEAR,
            TAYLOR_EXPANSION,
            SECANT_APPROXIMATION
        };
        
        LinearizationStrategy selectLinearizationStrategy(NodePtr nonlinear_term) const;
    };

} // namespace OptiSMT
