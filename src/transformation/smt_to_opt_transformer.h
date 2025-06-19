#pragma once

#include "../common.h"
#include "../theory/theory_solver.h"
#include "../optimization/optimization_backend.h"
#include <memory>
#include <vector>
#include <unordered_map>
#include <unordered_set>

namespace OptiSMT {

    // 转换配置
    struct TransformationConfig {
        bool use_big_m;
        double default_big_m;
        bool preprocess_constraints;
        bool enable_constraint_simplification;
        bool enable_variable_elimination;
        bool enable_redundancy_removal;
        double floating_point_precision;
        size_t max_piecewise_segments;
        bool use_sos_constraints;
        bool use_indicator_constraints;
        
        TransformationConfig() 
            : use_big_m(true), default_big_m(1e6), preprocess_constraints(true),
              enable_constraint_simplification(true), enable_variable_elimination(true),
              enable_redundancy_removal(true), floating_point_precision(1e-10),
              max_piecewise_segments(100), use_sos_constraints(true),
              use_indicator_constraints(true) {}
    };

    // 转换统计信息
    struct TransformationStatistics {
        size_t num_original_constraints;
        size_t num_transformed_constraints;
        size_t num_auxiliary_variables;
        size_t num_big_m_constraints;
        size_t num_sos_constraints;
        size_t num_indicator_constraints;
        double transformation_time;
        std::unordered_map<std::string, size_t> theory_constraint_counts;
        
        TransformationStatistics() 
            : num_original_constraints(0), num_transformed_constraints(0),
              num_auxiliary_variables(0), num_big_m_constraints(0),
              num_sos_constraints(0), num_indicator_constraints(0),
              transformation_time(0.0) {}
    };

    // SMT到优化问题转换器
    class SMTToOptTransformer {
    private:
        TransformationConfig config_;
        TransformationStatistics stats_;
        
        // 理论求解器
        std::unique_ptr<LinearArithmeticSolver> la_solver_;
        std::unique_ptr<BitVectorSolver> bv_solver_;
        std::unique_ptr<NonlinearArithmeticSolver> na_solver_;
        std::unique_ptr<FloatingPointSolver> fp_solver_;
        
        // 变量和约束管理
        std::unordered_map<std::string, NodePtr> smt_variables_;
        std::unordered_map<std::string, OptimizationVariable> opt_variables_;
        std::vector<LinearConstraint> opt_constraints_;
        std::unordered_set<std::string> auxiliary_variables_;
        
        // 布尔变量处理
        std::unordered_map<NodePtr, std::string> boolean_encoding_;
        std::vector<std::string> boolean_variables_;
        
        // BigM值管理
        std::unordered_map<NodePtr, double> constraint_big_m_values_;
        
    public:
        explicit SMTToOptTransformer(const TransformationConfig& config = TransformationConfig());
        ~SMTToOptTransformer() = default;
        
        // 主要转换接口
        bool transformSMTInstance(ParserPtr parser, OptimizationBackend_Base* backend);
        bool transformConstraints(const std::vector<NodePtr>& constraints, OptimizationBackend_Base* backend);
        bool transformSingleConstraint(NodePtr constraint, OptimizationBackend_Base* backend);
        
        // 变量处理
        bool extractAndDeclareVariables(const std::vector<NodePtr>& constraints);
        bool declareVariable(const std::string& name, NodePtr var_node);
        
        // 约束转换
        bool transformConstraint(NodePtr constraint);
        bool transformBooleanConstraint(NodePtr constraint);
        bool transformArithmeticConstraint(NodePtr constraint);
        bool transformBitVectorConstraint(NodePtr constraint);
        bool transformFloatingPointConstraint(NodePtr constraint);
        
        // 布尔编码
        std::string encodeBooleanFormula(NodePtr formula);
        std::string createBooleanVariable(NodePtr boolean_expr);
        bool addBooleanVariableConstraints(const std::string& bool_var);
        
        // BigM方法
        bool computeBigMValues(const std::vector<NodePtr>& constraints);
        double getBigMValue(NodePtr constraint);
        bool transformWithBigM(NodePtr constraint, const std::string& indicator_var);
        
        // 预处理
        bool preprocessConstraints(std::vector<NodePtr>& constraints);
        bool simplifyConstraints(std::vector<NodePtr>& constraints);
        bool eliminateRedundantConstraints(std::vector<NodePtr>& constraints);
        bool eliminateVariables(std::vector<NodePtr>& constraints);
        
        // 目标函数处理
        bool setObjectiveFromSMT(const std::vector<std::shared_ptr<SMTParser::Objective>>& objectives, OptimizationBackend_Base* backend);
        bool createFeasibilityObjective(OptimizationBackend_Base* backend);
        
        // 配置和统计
        void setConfig(const TransformationConfig& config);
        TransformationConfig getConfig() const;
        TransformationStatistics getStatistics() const;
        void resetStatistics();
        
        // 调试和诊断
        void printTransformationDetails();
        void dumpIntermediateResults(const std::string& filename);
        
    private:
        // 内部辅助方法
        TheorySolver* getAppropriateTheorySolver(NodePtr node);
        bool initializeTheorySolvers();
        
        // 约束分类
        bool classifyConstraints(const std::vector<NodePtr>& constraints,
                               std::vector<NodePtr>& linear_constraints,
                               std::vector<NodePtr>& nonlinear_constraints,
                               std::vector<NodePtr>& boolean_constraints,
                               std::vector<NodePtr>& bitvector_constraints,
                               std::vector<NodePtr>& floating_point_constraints);
        
        // 变量分析
        void analyzeVariables(const std::vector<NodePtr>& constraints);
        void collectVariables(NodePtr node, std::unordered_set<std::string>& variables);
        bool inferVariableBounds(const std::string& var_name, double& lower, double& upper);
        
        // 约束转换辅助
        bool transformLinearConstraints(const std::vector<NodePtr>& constraints);
        bool transformNonlinearConstraints(const std::vector<NodePtr>& constraints);
        bool transformBooleanConstraints(const std::vector<NodePtr>& constraints);
        
        // 布尔逻辑处理
        std::string transformAndConstraint(NodePtr and_node);
        std::string transformOrConstraint(NodePtr or_node);
        std::string transformNotConstraint(NodePtr not_node);
        std::string transformImpliesConstraint(NodePtr implies_node);
        std::string transformIteConstraint(NodePtr ite_node);
        
        // 辅助变量管理
        std::string generateAuxiliaryVariable(const std::string& prefix = "aux");
        bool addAuxiliaryVariableConstraints(const std::string& aux_var, NodePtr definition);
        
        // 错误处理
        void reportTransformationError(const std::string& message, NodePtr problematic_node = nullptr);
        bool isTransformationSupported(NodePtr node);
        
        // 性能优化
        void optimizeConstraintOrder(std::vector<NodePtr>& constraints);
        void mergeEquivalentConstraints(std::vector<NodePtr>& constraints);
        
        // 线性性检查
        bool isLinearExpression(NodePtr expr) const;
        
        // 统计更新
        void updateStatistics(const std::string& operation, size_t count = 1);
        void startTimer();
        void stopTimer();
        
    private:
        std::chrono::high_resolution_clock::time_point timer_start_;
    };

} // namespace OptiSMT 