#include "optismt.h"
#include "optimization/gurobi_backend.h"
#include <iostream>
#include <stdexcept>

namespace OptiSMT {

// OptiSMTSolver 实现
OptiSMTSolver::OptiSMTSolver(OptimizationBackend backend)
    : backend_type_(backend), last_result_(SolverResult::UNKNOWN), objective_value_(0.0) {
    
    // 创建SMT解析器
    parser_ = std::make_shared<SMTParser::Parser>();
    
    // 初始化组件
    if (!initializeBackend()) {
        throw std::runtime_error("Failed to initialize optimization backend");
    }
    
    if (!initializeTransformer()) {
        throw std::runtime_error("Failed to initialize SMT transformer");
    }
}

OptiSMTSolver::~OptiSMTSolver() = default;

bool OptiSMTSolver::loadSMTFile(const std::string& filename) {
    if (!parser_) {
        reportError("Parser not initialized");
        return false;
    }
    
    if (!parser_->parse(filename)) {
        reportError("Failed to parse SMT file: " + filename);
        return false;
    }
    
    return extractVariablesAndConstraints();
}

bool OptiSMTSolver::parseConstraints(const std::string& constraints) {
    if (!parser_) {
        reportError("Parser not initialized");
        return false;
    }
    
    if (!parser_->parseStr(constraints)) {
        reportError("Failed to parse constraints");
        return false;
    }
    
    return extractVariablesAndConstraints();
}

SolverResult OptiSMTSolver::solve() {
    if (!checkInitialization()) {
        return SolverResult::ERROR;
    }
    
    // 执行转换
    if (!performTransformation()) {
        reportError("Failed to transform SMT to optimization problem");
        return SolverResult::ERROR;
    }
    
    // 设置优化问题
    if (!setupOptimizationProblem()) {
        reportError("Failed to setup optimization problem");
        return SolverResult::ERROR;
    }
    
    // 求解
    SolveStatus status = opt_backend_->solve();
    last_result_ = convertSolveStatus(status);
    
    // 如果求解成功，获取结果
    if (last_result_ == SolverResult::SAT) {
        opt_backend_->getSolution(solution_);
        opt_backend_->getObjectiveValue(objective_value_);
    }
    
    return last_result_;
}

SolverResult OptiSMTSolver::checkSat() {
    return solve();
}

bool OptiSMTSolver::getModel(std::unordered_map<std::string, double>& model) {
    if (last_result_ != SolverResult::SAT) {
        return false;
    }
    
    model = solution_;
    return true;
}

bool OptiSMTSolver::getObjectiveValue(double& value) {
    if (last_result_ != SolverResult::SAT) {
        return false;
    }
    
    value = objective_value_;
    return true;
}

std::string OptiSMTSolver::getResultString() const {
    switch (last_result_) {
        case SolverResult::SAT: return "SAT";
        case SolverResult::UNSAT: return "UNSAT";
        case SolverResult::UNKNOWN: return "UNKNOWN";
        case SolverResult::ERROR: return "ERROR";
        default: return "UNKNOWN";
    }
}

void OptiSMTSolver::setOptimizationBackend(OptimizationBackend backend) {
    backend_type_ = backend;
    initializeBackend();
}

void OptiSMTSolver::setUseBigM(bool use_big_m) {
    transformation_config_.use_big_m = use_big_m;
    if (transformer_) {
        transformer_->setConfig(transformation_config_);
    }
}

void OptiSMTSolver::setDefaultBigM(double big_m) {
    transformation_config_.default_big_m = big_m;
    if (transformer_) {
        transformer_->setConfig(transformation_config_);
    }
}

void OptiSMTSolver::setPreprocessConstraints(bool preprocess) {
    transformation_config_.preprocess_constraints = preprocess;
    if (transformer_) {
        transformer_->setConfig(transformation_config_);
    }
}

void OptiSMTSolver::setTransformationConfig(const TransformationConfig& config) {
    transformation_config_ = config;
    if (transformer_) {
        transformer_->setConfig(transformation_config_);
    }
}

bool OptiSMTSolver::setOptimizerParameter(const std::string& param_name, double value) {
    if (!opt_backend_) {
        return false;
    }
    return opt_backend_->setParameter(param_name, value);
}

bool OptiSMTSolver::setOptimizerParameter(const std::string& param_name, int value) {
    if (!opt_backend_) {
        return false;
    }
    return opt_backend_->setParameter(param_name, value);
}

bool OptiSMTSolver::setOptimizerParameter(const std::string& param_name, const std::string& value) {
    if (!opt_backend_) {
        return false;
    }
    return opt_backend_->setParameter(param_name, value);
}

bool OptiSMTSolver::setTimeLimit(double time_limit) {
    return setOptimizerParameter("TimeLimit", time_limit);
}

bool OptiSMTSolver::setMIPGap(double gap) {
    return setOptimizerParameter("MIPGap", gap);
}

void OptiSMTSolver::dumpOptimizationModel(const std::string& filename) {
    if (opt_backend_) {
        opt_backend_->exportModel(filename);
    }
}

void OptiSMTSolver::printStatistics() {
    if (!opt_backend_) {
        std::cout << "Optimization backend not initialized" << std::endl;
        return;
    }
    
    std::cout << "=== OptiSMT Statistics ===" << std::endl;
    std::cout << "Backend: " << opt_backend_->getBackendName() << std::endl;
    std::cout << "Variables: " << variables_.size() << std::endl;
    std::cout << "Constraints: " << constraints_.size() << std::endl;
    std::cout << "Last Result: " << getResultString() << std::endl;
    
    if (last_result_ == SolverResult::SAT) {
        std::cout << "Solution variables: " << solution_.size() << std::endl;
        if (solution_.find("__objective__") != solution_.end()) {
            std::cout << "Objective value: " << objective_value_ << std::endl;
        }
    }
    
    opt_backend_->printStatistics();
}

void OptiSMTSolver::printTransformationStatistics() {
    if (transformer_) {
        auto stats = transformer_->getStatistics();
        std::cout << "=== Transformation Statistics ===" << std::endl;
        std::cout << "Original constraints: " << stats.num_original_constraints << std::endl;
        std::cout << "Transformed constraints: " << stats.num_transformed_constraints << std::endl;
        std::cout << "Auxiliary variables: " << stats.num_auxiliary_variables << std::endl;
        std::cout << "BigM constraints: " << stats.num_big_m_constraints << std::endl;
        std::cout << "SOS constraints: " << stats.num_sos_constraints << std::endl;
        std::cout << "Indicator constraints: " << stats.num_indicator_constraints << std::endl;
        std::cout << "Transformation time: " << stats.transformation_time << " seconds" << std::endl;
        
        if (!stats.theory_constraint_counts.empty()) {
            std::cout << "\nConstraints by theory:" << std::endl;
            for (const auto& [theory, count] : stats.theory_constraint_counts) {
                std::cout << "  " << theory << ": " << count << std::endl;
            }
        }
    }
}

TransformationStatistics OptiSMTSolver::getTransformationStatistics() const {
    if (transformer_) {
        return transformer_->getStatistics();
    }
    return TransformationStatistics{};
}

bool OptiSMTSolver::addUserConstraint(const std::string& constraint) {
    // 这是一个简化的实现，实际需要解析约束
    std::cout << "Adding user constraint: " << constraint << std::endl;
    return true;
}

bool OptiSMTSolver::addUserVariable(const std::string& name, const std::string& type, double lb, double ub) {
    // 这是一个简化的实现
    std::cout << "Adding user variable: " << name << " (" << type << ") [" << lb << ", " << ub << "]" << std::endl;
    return true;
}

bool OptiSMTSolver::setObjective(const std::string& objective_expr, ObjectiveType type) {
    // 这是一个简化的实现
    std::cout << "Setting objective: " << objective_expr << std::endl;
    return true;
}

bool OptiSMTSolver::pushScope() {
    // 增量求解功能的简化实现
    return true;
}

bool OptiSMTSolver::popScope() {
    // 增量求解功能的简化实现
    return true;
}

void OptiSMTSolver::reset() {
    variables_.clear();
    constraints_.clear();
    var_name_to_index_.clear();
    solution_.clear();
    last_result_ = SolverResult::UNKNOWN;
    objective_value_ = 0.0;
    
    if (opt_backend_) {
        opt_backend_->reset();
    }
    
    if (transformer_) {
        transformer_->resetStatistics();
    }
}

// 私有方法实现
bool OptiSMTSolver::initializeBackend() {
    opt_backend_ = createBackend(backend_type_);
    if (!opt_backend_) {
        return false;
    }
    
    return opt_backend_->initialize();
}

bool OptiSMTSolver::initializeTransformer() {
    transformer_ = std::make_unique<SMTToOptTransformer>(transformation_config_);
    return transformer_ != nullptr;
}

bool OptiSMTSolver::extractVariablesAndConstraints() {
    if (!parser_) {
        return false;
    }
    
    // 提取变量
    auto declared_vars = parser_->getDeclaredVariables();
    for (const auto& var : declared_vars) {
        if (var && !var->getName().empty()) {
            VariableInfo var_info(var->getName(), var);
            variables_.push_back(var_info);
            var_name_to_index_[var->getName()] = variables_.size() - 1;
        }
    }
    
    // 提取约束
    auto assertions = parser_->getAssertions();
    for (const auto& assertion : assertions) {
        if (assertion) {
            ConstraintInfo constraint_info(assertion);
            constraints_.push_back(constraint_info);
        }
    }
    
    return true;
}

bool OptiSMTSolver::performTransformation() {
    if (!transformer_ || !opt_backend_) {
        return false;
    }
    
    // 提取约束
    std::vector<NodePtr> smt_constraints;
    for (const auto& constraint_info : constraints_) {
        smt_constraints.push_back(constraint_info.smt_constraint);
    }
    
    // 执行转换
    return transformer_->transformConstraints(smt_constraints, opt_backend_.get());
}

bool OptiSMTSolver::setupOptimizationProblem() {
    // 这里应该设置目标函数，如果有的话
    auto objectives = parser_->getObjectives();
    if (!objectives.empty()) {
        transformer_->setObjectiveFromSMT(objectives, opt_backend_.get());
    } else {
        // 如果没有目标函数，创建一个可行性目标
        transformer_->createFeasibilityObjective(opt_backend_.get());
    }
    
    return true;
}

SolverResult OptiSMTSolver::convertSolveStatus(SolveStatus status) {
    switch (status) {
        case SolveStatus::OPTIMAL: return SolverResult::SAT;
        case SolveStatus::INFEASIBLE: return SolverResult::UNSAT;
        case SolveStatus::UNBOUNDED: return SolverResult::SAT;  // 无界但可行
        case SolveStatus::TIME_LIMIT:
        case SolveStatus::ITERATION_LIMIT:
        case SolveStatus::UNKNOWN: return SolverResult::UNKNOWN;
        case SolveStatus::ERROR: return SolverResult::ERROR;
        default: return SolverResult::UNKNOWN;
    }
}

std::unique_ptr<OptimizationBackend_Base> OptiSMTSolver::createBackend(OptimizationBackend type) {
    switch (type) {
        case OptimizationBackend::GUROBI:
            return std::make_unique<GurobiBackend>();
        case OptimizationBackend::CPLEX:
            // TODO: 实现CPLEX后端
            std::cerr << "CPLEX backend not yet implemented" << std::endl;
            return nullptr;
        case OptimizationBackend::Z3_OPTIMIZE:
            // TODO: 实现Z3后端
            std::cerr << "Z3 backend not yet implemented" << std::endl;
            return nullptr;
        case OptimizationBackend::SCIP:
            // TODO: 实现SCIP后端
            std::cerr << "SCIP backend not yet implemented" << std::endl;
            return nullptr;
        default:
            return nullptr;
    }
}

void OptiSMTSolver::reportError(const std::string& message) {
    std::cerr << "OptiSMT Error: " << message << std::endl;
}

bool OptiSMTSolver::checkInitialization() const {
    if (!parser_) {
        std::cerr << "Parser not initialized" << std::endl;
        return false;
    }
    
    if (!transformer_) {
        std::cerr << "Transformer not initialized" << std::endl;
        return false;
    }
    
    if (!opt_backend_) {
        std::cerr << "Optimization backend not initialized" << std::endl;
        return false;
    }
    
    return true;
}

// 工厂函数实现
std::unique_ptr<OptiSMTSolver> createOptiSMTSolver(OptimizationBackend backend) {
    try {
        return std::make_unique<OptiSMTSolver>(backend);
    } catch (const std::exception& e) {
        std::cerr << "Failed to create OptiSMT solver: " << e.what() << std::endl;
        return nullptr;
    }
}

} // namespace OptiSMT
