#pragma once

#include "../common.h"
#include <vector>
#include <string>
#include <unordered_map>

namespace OptiSMT {

    // 转换结果
    struct TransformationResult {
        std::vector<std::string> linear_constraints;     // 线性约束
        std::vector<std::string> nonlinear_constraints;  // 非线性约束
        std::vector<std::string> auxiliary_variables;    // 辅助变量
        std::vector<std::string> variable_bounds;        // 变量边界
        std::unordered_map<std::string, std::string> variable_mapping;  // SMT变量到优化变量的映射
        bool success;
        std::string error_message;
        
        TransformationResult() : success(false) {}
    };

    // 理论求解器抽象基类
    class TheorySolver {
    public:
        virtual ~TheorySolver() = default;
        
        // 主要转换接口
        virtual TransformationResult transformConstraint(NodePtr constraint) = 0;
        virtual TransformationResult transformConstraints(const std::vector<NodePtr>& constraints) = 0;
        
        // 变量处理
        virtual bool declareVariable(const std::string& name, NodePtr var_node) = 0;
        virtual std::vector<std::string> getVariables() const = 0;
        virtual std::string getVariableType(const std::string& name) const = 0;
        
        // BigM方法支持
        virtual double computeBigM(NodePtr constraint) = 0;
        virtual bool supportsBigM() const = 0;
        
        // 辅助方法
        virtual bool canHandle(NodePtr node) const = 0;
        virtual std::string getTheoryName() const = 0;
        virtual void reset() = 0;
        
        // 预处理
        virtual NodePtr preprocessConstraint(NodePtr constraint) = 0;
        virtual bool simplifyConstraint(NodePtr& constraint) = 0;
        
    protected:
        // 通用辅助方法
        std::string generateAuxiliaryVariableName();
        std::string nodeToString(NodePtr node);
        bool isLinearTerm(NodePtr node);
        bool containsVariable(NodePtr node, const std::string& var_name);
        
    private:
        static size_t aux_var_counter_;
    };



} // namespace OptiSMT 