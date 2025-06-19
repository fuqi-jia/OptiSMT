#pragma once

#include "../theory_solver.h"
#include <unordered_set>

namespace OptiSMT {

    // 浮点数理论求解器
    class FloatingPointSolver : public TheorySolver {
    private:
        std::unordered_map<std::string, NodePtr> declared_variables_;
        std::unordered_map<std::string, std::pair<size_t, size_t>> fp_formats_;  // (exponent_bits, significand_bits)
        
        // 浮点数近似参数
        double floating_point_precision_;
        bool use_interval_arithmetic_;
        
    public:
        FloatingPointSolver() : floating_point_precision_(1e-15), use_interval_arithmetic_(false) {}
        ~FloatingPointSolver() override = default;
        
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
        std::string getTheoryName() const override { return "FloatingPoint"; }
        void reset() override;
        
        // 预处理
        NodePtr preprocessConstraint(NodePtr constraint) override;
        bool simplifyConstraint(NodePtr& constraint) override;
        
        // 配置方法
        void setFloatingPointPrecision(double precision);
        void setUseIntervalArithmetic(bool use_interval);
        
    private:
        // 浮点数转换方法
        std::string transformFloatingPointTerm(NodePtr term);
        std::string transformFloatingPointConstraint(NodePtr constraint);
        std::string transformFloatingPointComparison(NodePtr constraint);
        
        // 浮点数算术操作
        std::string transformFloatingPointAdd(NodePtr node);
        std::string transformFloatingPointSub(NodePtr node);
        std::string transformFloatingPointMul(NodePtr node);
        std::string transformFloatingPointDiv(NodePtr node);
        std::string transformFloatingPointSqrt(NodePtr node);
        std::string transformFloatingPointAbs(NodePtr node);
        std::string transformFloatingPointNeg(NodePtr node);
        
        // 浮点数比较操作
        std::string transformFloatingPointEquals(NodePtr node);
        std::string transformFloatingPointLess(NodePtr node);
        std::string transformFloatingPointGreater(NodePtr node);
        
        // 浮点数特殊值处理
        std::string handleFloatingPointSpecialValues(NodePtr node);
        std::string transformFloatingPointIsNaN(NodePtr node);
        std::string transformFloatingPointIsInfinite(NodePtr node);
        std::string transformFloatingPointIsZero(NodePtr node);
        std::string transformFloatingPointIsNormal(NodePtr node);
        std::string transformFloatingPointIsSubnormal(NodePtr node);
        
        // 舍入模式处理
        std::string transformWithRoundingMode(NodePtr node, const std::string& rounding_mode);
        
        // 浮点数到实数转换
        std::string convertFloatingPointToReal(NodePtr fp_node);
        std::string convertRealToFloatingPoint(NodePtr real_node, size_t exp_bits, size_t sig_bits);
        
        // 区间算术支持
        std::string createIntervalConstraints(const std::string& fp_var, double lower, double upper);
        
        // 误差分析
        std::string addRoundingErrorConstraints(const std::string& exact_var, const std::string& fp_var);
        double estimateRoundingError(size_t exp_bits, size_t sig_bits, double value) const;
        
        // 辅助方法
        std::pair<size_t, size_t> getFloatingPointFormat(NodePtr node) const;
        std::pair<size_t, size_t> getFloatingPointFormat(const std::string& var_name) const;
        bool isFloatingPointConstant(NodePtr node) const;
        double getFloatingPointConstantValue(NodePtr node) const;
        
        // 浮点数边界估计
        std::pair<double, double> estimateFloatingPointBounds(size_t exp_bits, size_t sig_bits) const;
        double getMaxFiniteValue(size_t exp_bits, size_t sig_bits) const;
        double getMinNormalValue(size_t exp_bits, size_t sig_bits) const;
        
        // 舍入模式枚举
        enum class RoundingMode {
            ROUND_NEAREST_TIES_TO_EVEN,
            ROUND_NEAREST_TIES_AWAY,
            ROUND_TOWARD_POSITIVE,
            ROUND_TOWARD_NEGATIVE,
            ROUND_TOWARD_ZERO
        };
        
        RoundingMode parseRoundingMode(NodePtr rounding_node) const;
        std::string roundingModeToString(RoundingMode mode) const;
    };

} // namespace OptiSMT
