#pragma once

#include "../common.h"
#include <vector>
#include <string>
#include <unordered_map>

namespace OptiSMT {

    // 变量类型
    enum class VariableType {
        CONTINUOUS,
        INTEGER,
        BINARY
    };

    // 约束类型
    enum class ConstraintType {
        LESS_EQUAL,      // <=
        GREATER_EQUAL,   // >=
        EQUAL,           // =
        LESS,            // <
        GREATER          // >
    };

    // 优化目标类型
    enum class ObjectiveType {
        MINIMIZE,
        MAXIMIZE,
        FEASIBILITY  // 只求可行解
    };

    // 求解状态
    enum class SolveStatus {
        OPTIMAL,
        INFEASIBLE,
        UNBOUNDED,
        TIME_LIMIT,
        ITERATION_LIMIT,
        ERROR,
        UNKNOWN
    };

    // 线性约束
    struct LinearConstraint {
        std::vector<std::pair<std::string, double>> coefficients;  // (variable_name, coefficient)
        ConstraintType type;
        double rhs;
        std::string name;
        
        LinearConstraint(ConstraintType t, double r) : type(t), rhs(r) {}
    };

    // 目标函数
    struct ObjectiveFunction {
        std::vector<std::pair<std::string, double>> coefficients;  // (variable_name, coefficient)
        ObjectiveType type;
        std::string name;
        
        // 默认构造函数
        ObjectiveFunction() : type(ObjectiveType::FEASIBILITY) {}
        
        ObjectiveFunction(ObjectiveType t) : type(t) {}
    };

    // 优化变量
    struct OptimizationVariable {
        std::string name;
        VariableType type;
        double lower_bound;
        double upper_bound;
        
        // 默认构造函数
        OptimizationVariable() 
            : name(""), type(VariableType::CONTINUOUS), lower_bound(-1e20), upper_bound(1e20) {}
        
        OptimizationVariable(const std::string& n, VariableType t, double lb = -1e20, double ub = 1e20)
            : name(n), type(t), lower_bound(lb), upper_bound(ub) {}
    };

    // 优化后端抽象基类
    class OptimizationBackend_Base {
    public:
        virtual ~OptimizationBackend_Base() = default;
        
        // 模型构建
        virtual bool initialize() = 0;
        virtual bool addVariable(const OptimizationVariable& var) = 0;
        virtual bool addConstraint(const LinearConstraint& constraint) = 0;
        virtual bool setObjective(const ObjectiveFunction& objective) = 0;
        
        // 求解
        virtual SolveStatus solve() = 0;
        virtual SolveStatus solve(double time_limit) = 0;
        
        // 结果获取
        virtual bool getSolution(std::unordered_map<std::string, double>& solution) = 0;
        virtual bool getObjectiveValue(double& value) = 0;
        virtual double getDualValue(const std::string& constraint_name) = 0;
        virtual double getReducedCost(const std::string& variable_name) = 0;
        
        // 模型信息
        virtual size_t getNumVariables() const = 0;
        virtual size_t getNumConstraints() const = 0;
        virtual std::string getStatusString() const = 0;
        
        // 参数设置
        virtual bool setParameter(const std::string& param_name, double value) = 0;
        virtual bool setParameter(const std::string& param_name, int value) = 0;
        virtual bool setParameter(const std::string& param_name, const std::string& value) = 0;
        
        // 模型导出
        virtual bool exportModel(const std::string& filename) = 0;
        virtual bool importModel(const std::string& filename) = 0;
        
        // 调试和诊断
        virtual void printStatistics() = 0;
        virtual std::string getBackendName() const = 0;
        virtual std::string getVersion() const = 0;
        
        // 高级功能
        virtual bool addSOS1Constraint(const std::vector<std::string>& variables) = 0;
        virtual bool addSOS2Constraint(const std::vector<std::string>& variables) = 0;
        virtual bool addIndicatorConstraint(const std::string& binary_var, bool binary_value, const LinearConstraint& constraint) = 0;
        
        // 模型修改
        virtual bool removeVariable(const std::string& var_name) = 0;
        virtual bool removeConstraint(const std::string& constraint_name) = 0;
        virtual bool updateVariableBounds(const std::string& var_name, double lower, double upper) = 0;
        virtual bool updateConstraintRHS(const std::string& constraint_name, double new_rhs) = 0;
        
        // 清理
        virtual void reset() = 0;
    };

} // namespace OptiSMT 