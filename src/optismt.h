#pragma once

#include "common.h"
#include "theory/theory_solver.h"
#include "theory/la/la.h"
#include "theory/bv/bv.h"
#include "theory/na/na.h"
#include "theory/fp/fp.h"
#include "optimization/optimization_backend.h"
#include "transformation/smt_to_opt_transformer.h"
#include <memory>
#include <vector>
#include <unordered_map>
#include <string>

namespace OptiSMT {

    // 求解结果类型
    enum class SolverResult {
        SAT,
        UNSAT,
        UNKNOWN,
        ERROR
    };

    // 优化后端类型
    enum class OptimizationBackend {
        GUROBI,
        CPLEX,
        Z3_OPTIMIZE,
        SCIP
    };

    // 变量信息
    struct VariableInfo {
        std::string name;
        NodePtr smt_node;
        std::string opt_var_name;  // 在优化求解器中的变量名
        bool is_integer;
        bool is_boolean;
        double lower_bound;
        double upper_bound;
        
        VariableInfo(const std::string& n, NodePtr node) 
            : name(n), smt_node(node), opt_var_name(n), 
              is_integer(false), is_boolean(false),
              lower_bound(-INFINITY_VALUE), upper_bound(INFINITY_VALUE) {}
    };

    // 约束信息
    struct ConstraintInfo {
        NodePtr smt_constraint;
        std::string opt_constraint;  // 转换后的优化约束
        double big_m_value;         // BigM方法中的M值
        bool is_hard;               // 硬约束或软约束
        double weight;              // 软约束权重
        
        ConstraintInfo(NodePtr constraint) 
            : smt_constraint(constraint), big_m_value(DEFAULT_BIG_M), 
              is_hard(true), weight(1.0) {}
    };

    // 主求解器类
    class OptiSMTSolver {
    private:
        ParserPtr parser_;
        std::unique_ptr<SMTToOptTransformer> transformer_;
        std::unique_ptr<OptimizationBackend_Base> opt_backend_;
        
        // 变量和约束管理
        std::vector<VariableInfo> variables_;
        std::vector<ConstraintInfo> constraints_;
        std::unordered_map<std::string, size_t> var_name_to_index_;
        
        // 配置选项
        OptimizationBackend backend_type_;
        TransformationConfig transformation_config_;
        
        // 求解结果
        SolverResult last_result_;
        std::unordered_map<std::string, double> solution_;
        double objective_value_;
        
    public:
        explicit OptiSMTSolver(OptimizationBackend backend = OptimizationBackend::GUROBI);
        ~OptiSMTSolver();
        
        // 文件解析
        bool loadSMTFile(const std::string& filename);
        bool parseConstraints(const std::string& constraints);
        
        // 主求解接口
        SolverResult solve();
        SolverResult checkSat();
        
        // 结果获取
        bool getModel(std::unordered_map<std::string, double>& model);
        bool getObjectiveValue(double& value);
        std::string getResultString() const;
        
        // 配置设置
        void setOptimizationBackend(OptimizationBackend backend);
        void setUseBigM(bool use_big_m);
        void setDefaultBigM(double big_m);
        void setPreprocessConstraints(bool preprocess);
        void setTransformationConfig(const TransformationConfig& config);
        
        // 参数设置
        bool setOptimizerParameter(const std::string& param_name, double value);
        bool setOptimizerParameter(const std::string& param_name, int value);
        bool setOptimizerParameter(const std::string& param_name, const std::string& value);
        bool setTimeLimit(double time_limit);
        bool setMIPGap(double gap);
        
        // 调试和诊断
        void dumpOptimizationModel(const std::string& filename);
        void printStatistics();
        void printTransformationStatistics();
        TransformationStatistics getTransformationStatistics() const;
        
        // 高级功能
        bool addUserConstraint(const std::string& constraint);
        bool addUserVariable(const std::string& name, const std::string& type, double lb = -INFINITY_VALUE, double ub = INFINITY_VALUE);
        bool setObjective(const std::string& objective_expr, ObjectiveType type = ObjectiveType::MINIMIZE);
        
        // 增量求解支持
        bool pushScope();
        bool popScope();
        void reset();
        
    private:
        // 内部方法
        bool initializeBackend();
        bool initializeTransformer();
        bool extractVariablesAndConstraints();
        bool performTransformation();
        bool setupOptimizationProblem();
        SolverResult convertSolveStatus(SolveStatus status);
        
        // 工厂方法
        std::unique_ptr<OptimizationBackend_Base> createBackend(OptimizationBackend type);
        
        // 错误处理
        void reportError(const std::string& message);
        bool checkInitialization() const;
    };

    // 工厂函数
    std::unique_ptr<OptiSMTSolver> createOptiSMTSolver(OptimizationBackend backend = OptimizationBackend::GUROBI);

} // namespace OptiSMT