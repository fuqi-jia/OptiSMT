#pragma once

#include "optimization_backend.h"
#include <memory>

// 前向声明Gurobi类型，避免包含Gurobi头文件
struct GRBenv;
struct GRBmodel;

namespace OptiSMT {

    // Gurobi优化后端
    class GurobiBackend : public OptimizationBackend_Base {
    private:
        GRBenv* env_;
        GRBmodel* model_;
        std::unordered_map<std::string, int> variable_indices_;
        std::unordered_map<std::string, int> constraint_indices_;
        bool initialized_;
        SolveStatus last_status_;
        
    public:
        GurobiBackend();
        ~GurobiBackend() override;
        
        // 实现基类接口
        bool initialize() override;
        bool addVariable(const OptimizationVariable& var) override;
        bool addConstraint(const LinearConstraint& constraint) override;
        bool setObjective(const ObjectiveFunction& objective) override;
        
        // 求解
        SolveStatus solve() override;
        SolveStatus solve(double time_limit) override;
        
        // 结果获取
        bool getSolution(std::unordered_map<std::string, double>& solution) override;
        bool getObjectiveValue(double& value) override;
        double getDualValue(const std::string& constraint_name) override;
        double getReducedCost(const std::string& variable_name) override;
        
        // 模型信息
        size_t getNumVariables() const override;
        size_t getNumConstraints() const override;
        std::string getStatusString() const override;
        
        // 参数设置
        bool setParameter(const std::string& param_name, double value) override;
        bool setParameter(const std::string& param_name, int value) override;
        bool setParameter(const std::string& param_name, const std::string& value) override;
        
        // 模型导出
        bool exportModel(const std::string& filename) override;
        bool importModel(const std::string& filename) override;
        
        // 调试和诊断
        void printStatistics() override;
        std::string getBackendName() const override { return "Gurobi"; }
        std::string getVersion() const override;
        
        // 高级功能
        bool addSOS1Constraint(const std::vector<std::string>& variables) override;
        bool addSOS2Constraint(const std::vector<std::string>& variables) override;
        bool addIndicatorConstraint(const std::string& binary_var, bool binary_value, const LinearConstraint& constraint) override;
        
        // 模型修改
        bool removeVariable(const std::string& var_name) override;
        bool removeConstraint(const std::string& constraint_name) override;
        bool updateVariableBounds(const std::string& var_name, double lower, double upper) override;
        bool updateConstraintRHS(const std::string& constraint_name, double new_rhs) override;
        
        // 清理
        void reset() override;
        
        // Gurobi特定方法
        bool setGurobiParameter(const std::string& param_name, double value);
        bool setGurobiParameter(const std::string& param_name, int value);
        bool setMIPGap(double gap);
        bool setTimeLimit(double time_limit);
        bool setThreads(int num_threads);
        bool setMethod(int method);  // 0=primal simplex, 1=dual simplex, 2=barrier, etc.
        
        // 回调函数支持
        bool setProgressCallback(std::function<bool(double progress, double obj_value)> callback);
        
        // IIS (Irreducible Inconsistent Subsystem) 计算
        bool computeIIS();
        std::vector<std::string> getIISConstraints();
        std::vector<std::string> getIISVariables();
        
    private:
        // 内部辅助方法
        bool checkGurobiError(int error_code, const std::string& operation);
        char convertVariableType(VariableType type);
        char convertConstraintType(ConstraintType type);
        int convertObjectiveType(ObjectiveType type);
        SolveStatus convertGurobiStatus(int gurobi_status);
        
        // 模型更新
        bool updateModel();
        
        // 变量索引管理
        int getVariableIndex(const std::string& var_name);
        int getConstraintIndex(const std::string& constraint_name);
        
        // 清理资源
        void cleanup();
    };

    // 工厂函数
    std::unique_ptr<OptimizationBackend_Base> createGurobiBackend();

} // namespace OptiSMT 