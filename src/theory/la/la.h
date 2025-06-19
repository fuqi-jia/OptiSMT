#pragma once

#include "../theory_solver.h"
#include <unordered_set>

namespace OptiSMT {

    // 线性算术理论求解器
    class LinearArithmeticSolver : public TheorySolver {
    private:
        std::unordered_map<std::string, NodePtr> declared_variables_;
        std::unordered_set<std::string> integer_variables_;
        std::unordered_set<std::string> real_variables_;
        
    public:
        LinearArithmeticSolver() = default;
        ~LinearArithmeticSolver() override = default;
        
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
        std::string getTheoryName() const override { return "LinearArithmetic"; }
        void reset() override;
        
        // 预处理
        NodePtr preprocessConstraint(NodePtr constraint) override;
        bool simplifyConstraint(NodePtr& constraint) override;
        
    private:
        // 内部转换方法
        std::string transformLinearTerm(NodePtr term);
        std::string transformArithmeticConstraint(NodePtr constraint);
        std::string transformComparisonConstraint(NodePtr constraint);
        std::string transformBooleanConstraint(NodePtr constraint);
        
        // 线性表达式处理
        bool isLinearExpression(NodePtr expr) const;
        std::string linearExpressionToString(NodePtr expr);
        
        // BigM转换
        std::string transformWithBigM(NodePtr constraint, const std::string& indicator_var);
        
        // 布尔变量转换
        std::string createBooleanVariableConstraints(const std::string& bool_var);
        
        // 辅助方法
        void collectVariables(NodePtr node, std::unordered_set<std::string>& vars) const;
        double estimateVariableBounds(const std::string& var_name) const;
        bool isIntegerVariable(const std::string& name) const;
    };

} // namespace OptiSMT
