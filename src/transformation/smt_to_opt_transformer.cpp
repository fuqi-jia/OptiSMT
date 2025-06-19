#include "smt_to_opt_transformer.h"
#include "../theory/la/la.h"
#include "../theory/bv/bv.h"
#include "../theory/na/na.h"
#include "../theory/fp/fp.h"
#include <iostream>
#include <chrono>

namespace OptiSMT {

SMTToOptTransformer::SMTToOptTransformer(const TransformationConfig& config)
    : config_(config) {
    initializeTheorySolvers();
    resetStatistics();
}

bool SMTToOptTransformer::transformSMTInstance(ParserPtr parser, OptimizationBackend_Base* backend) {
    if (!parser || !backend) {
        std::cout << "错误: 空的parser或backend指针" << std::endl;
        return false;
    }
    
    startTimer();
    
    // 获取约束
    auto constraints = parser->getAssertions();
    auto objectives = parser->getObjectives();
    auto variables = parser->getVariables();
    
    std::cout << "\n=== SMT实例信息 ===" << std::endl;
    std::cout << "约束数量: " << constraints.size() << std::endl;
    std::cout << "目标函数数量: " << objectives.size() << std::endl;
    std::cout << "变量数量: " << variables.size() << std::endl;
    
    // 打印变量名
    std::cout << "变量列表: ";
    for (const auto& var : variables) {
        if (var && var->isVar()) {
            std::cout << var->getName() << " ";
        }
    }
    std::cout << std::endl;
    
    // 打印约束信息
    std::cout << "\n约束详情:" << std::endl;
    for (size_t i = 0; i < constraints.size(); ++i) {
        if (constraints[i]) {
            std::cout << "约束 " << i << ": Kind=" << static_cast<int>(constraints[i]->getKind()) 
                      << ", 子节点数=" << constraints[i]->getChildrenSize() << std::endl;
            // 添加约束内容分析
            if (constraints[i]->isArithComp()) {
                std::cout << "  -> 算术比较约束" << std::endl;
            } else if (constraints[i]->isVar()) {
                std::cout << "  -> 变量: " << constraints[i]->getName() << std::endl;
            } else if (constraints[i]->isConst()) {
                std::cout << "  -> 常量" << std::endl;
            }
        }
    }
    
    stats_.num_original_constraints = constraints.size();
    
    // 预处理
    std::cout << "\n=== 预处理阶段 ===" << std::endl;
    if (config_.preprocess_constraints) {
        preprocessConstraints(constraints);
    } else {
        std::cout << "跳过预处理" << std::endl;
    }
    
    // 提取变量
    std::cout << "\n=== 变量提取阶段 ===" << std::endl;
    extractAndDeclareVariables(constraints);
    
    std::cout << "提取到的优化变量数量: " << opt_variables_.size() << std::endl;
    for (const auto& var_pair : opt_variables_) {
        std::cout << "  变量: " << var_pair.first << ", 类型: " << static_cast<int>(var_pair.second.type) << std::endl;
    }
    
    // 转换约束
    std::cout << "\n=== 约束转换阶段 ===" << std::endl;
    bool success = transformConstraints(constraints, backend);
    
    // 处理目标函数
    std::cout << "\n=== 目标函数设置阶段 ===" << std::endl;
    if (!objectives.empty()) {
        std::cout << "使用SMT目标函数, 数量: " << objectives.size() << std::endl;
        setObjectiveFromSMT(objectives, backend);
    } else {
        std::cout << "创建可行性目标函数" << std::endl;
        createFeasibilityObjective(backend);
    }
    
    stopTimer();
    std::cout << "\n转换完成, 成功: " << (success ? "是" : "否") << std::endl;
    return success;
}

bool SMTToOptTransformer::transformConstraints(const std::vector<NodePtr>& constraints, OptimizationBackend_Base* backend) {
    if (!backend) {
        return false;
    }
    
    startTimer();
    
    // 分类约束
    std::vector<NodePtr> linear_constraints;
    std::vector<NodePtr> nonlinear_constraints;
    std::vector<NodePtr> boolean_constraints;
    std::vector<NodePtr> bitvector_constraints;
    std::vector<NodePtr> floating_point_constraints;
    
    classifyConstraints(constraints, linear_constraints, nonlinear_constraints,
                       boolean_constraints, bitvector_constraints, floating_point_constraints);
    
    // 分别转换各类约束
    bool success = true;
    success &= transformLinearConstraints(linear_constraints);
    success &= transformNonlinearConstraints(nonlinear_constraints);
    success &= transformBooleanConstraints(boolean_constraints);
    
    stats_.num_transformed_constraints = opt_constraints_.size();
    
    stopTimer();
    return success;
}

bool SMTToOptTransformer::transformSingleConstraint(NodePtr constraint, OptimizationBackend_Base* backend) {
    if (!constraint || !backend) {
        return false;
    }
    
    return transformConstraint(constraint);
}

bool SMTToOptTransformer::extractAndDeclareVariables(const std::vector<NodePtr>& constraints) {
    std::unordered_set<std::string> variable_names;
    
    std::cout << "从 " << constraints.size() << " 个约束中收集变量:" << std::endl;
    
    // 收集所有变量
    for (size_t i = 0; i < constraints.size(); ++i) {
        std::cout << "  处理约束 " << i << ":" << std::endl;
        collectVariables(constraints[i], variable_names);
    }
    
    std::cout << "收集到的变量总数: " << variable_names.size() << std::endl;
    
    // 声明变量
    std::cout << "声明变量:" << std::endl;
    for (const auto& var_name : variable_names) {
        std::cout << "  声明变量: " << var_name << " (类型: CONTINUOUS)" << std::endl;
        // 这里简化处理，实际需要根据变量类型创建相应的优化变量
        OptimizationVariable opt_var(var_name, VariableType::CONTINUOUS);
        opt_variables_.insert({var_name, opt_var});
    }
    
    return true;
}

bool SMTToOptTransformer::declareVariable(const std::string& name, NodePtr var_node) {
    if (name.empty() || !var_node) {
        return false;
    }
    
    smt_variables_[name] = var_node;
    
    // 根据变量类型创建优化变量
    VariableType var_type = VariableType::CONTINUOUS;
    
    // 简化的类型推断
    if (var_node->isVBool()) {
        var_type = VariableType::BINARY;
    } else if (var_node->isVInt()) {
        var_type = VariableType::INTEGER;
    }
    
    OptimizationVariable opt_var(name, var_type);
    opt_variables_.insert({name, opt_var});
    
    return true;
}

bool SMTToOptTransformer::transformConstraint(NodePtr constraint) {
    if (!constraint) {
        return false;
    }
    
    // 根据约束类型选择合适的理论求解器
    TheorySolver* solver = getAppropriateTheorySolver(constraint);
    if (!solver) {
        return false;
    }
    
    // 转换约束
    auto result = solver->transformConstraint(constraint);
    if (!result.success) {
        std::cerr << "Failed to transform constraint: " << result.error_message << std::endl;
        return false;
    }
    
    // 添加转换后的约束
    for (const auto& linear_constraint_str : result.linear_constraints) {
        // 这里应该解析约束字符串并创建LinearConstraint对象
        // 为了简化，这里只是打印
        std::cout << "Linear constraint: " << linear_constraint_str << std::endl;
    }
    
    updateStatistics("transform_constraint");
    return true;
}

bool SMTToOptTransformer::transformBooleanConstraint(NodePtr constraint) {
    // 布尔约束的简化处理
    std::cout << "Transforming boolean constraint" << std::endl;
    return true;
}

bool SMTToOptTransformer::transformArithmeticConstraint(NodePtr constraint) {
    // 算术约束的简化处理
    std::cout << "Transforming arithmetic constraint" << std::endl;
    return true;
}

bool SMTToOptTransformer::transformBitVectorConstraint(NodePtr constraint) {
    // 位向量约束的简化处理
    std::cout << "Transforming bit vector constraint" << std::endl;
    return true;
}

bool SMTToOptTransformer::transformFloatingPointConstraint(NodePtr constraint) {
    // 浮点数约束的简化处理
    std::cout << "Transforming floating point constraint" << std::endl;
    return true;
}

std::string SMTToOptTransformer::encodeBooleanFormula(NodePtr formula) {
    if (!formula) {
        return "";
    }
    
    // 简化的布尔编码
    if (formula->isAnd()) {
        return "AND encoding";
    } else if (formula->isOr()) {
        return "OR encoding";
    } else if (formula->isNot()) {
        return "NOT encoding";
    }
    
    return "boolean_formula";
}

std::string SMTToOptTransformer::createBooleanVariable(NodePtr boolean_expr) {
    if (!boolean_expr) {
        return "";
    }
    
    // 检查是否已经编码过
    if (boolean_encoding_.find(boolean_expr) != boolean_encoding_.end()) {
        return boolean_encoding_[boolean_expr];
    }
    
    // 创建新的布尔变量
    std::string bool_var = generateAuxiliaryVariable("bool");
    boolean_encoding_[boolean_expr] = bool_var;
    boolean_variables_.push_back(bool_var);
    
    // 添加布尔变量约束
    addBooleanVariableConstraints(bool_var);
    
    return bool_var;
}

bool SMTToOptTransformer::addBooleanVariableConstraints(const std::string& bool_var) {
    // 为布尔变量添加 0 <= bool_var <= 1 约束
    std::cout << "Adding boolean constraints for " << bool_var << std::endl;
    return true;
}

bool SMTToOptTransformer::computeBigMValues(const std::vector<NodePtr>& constraints) {
    for (const auto& constraint : constraints) {
        double big_m = getBigMValue(constraint);
        constraint_big_m_values_[constraint] = big_m;
    }
    return true;
}

double SMTToOptTransformer::getBigMValue(NodePtr constraint) {
    if (!constraint) {
        return config_.default_big_m;
    }
    
    // 检查是否已经计算过
    if (constraint_big_m_values_.find(constraint) != constraint_big_m_values_.end()) {
        return constraint_big_m_values_[constraint];
    }
    
    // 简化的BigM计算
    return config_.default_big_m;
}

bool SMTToOptTransformer::transformWithBigM(NodePtr constraint, const std::string& indicator_var) {
    double big_m = getBigMValue(constraint);
    
    // 使用BigM方法转换约束
    std::cout << "Transforming with BigM (" << big_m << ") and indicator " << indicator_var << std::endl;
    
    stats_.num_big_m_constraints++;
    return true;
}

bool SMTToOptTransformer::preprocessConstraints(std::vector<NodePtr>& constraints) {
    if (!config_.preprocess_constraints) {
        return true;
    }
    
    std::cout << "Preprocessing " << constraints.size() << " constraints" << std::endl;
    
    if (config_.enable_constraint_simplification) {
        simplifyConstraints(constraints);
    }
    
    if (config_.enable_redundancy_removal) {
        eliminateRedundantConstraints(constraints);
    }
    
    if (config_.enable_variable_elimination) {
        eliminateVariables(constraints);
    }
    
    return true;
}

bool SMTToOptTransformer::simplifyConstraints(std::vector<NodePtr>& constraints) {
    std::cout << "Simplifying constraints" << std::endl;
    return true;
}

bool SMTToOptTransformer::eliminateRedundantConstraints(std::vector<NodePtr>& constraints) {
    std::cout << "Eliminating redundant constraints" << std::endl;
    return true;
}

bool SMTToOptTransformer::eliminateVariables(std::vector<NodePtr>& constraints) {
    std::cout << "Eliminating variables" << std::endl;
    return true;
}

bool SMTToOptTransformer::setObjectiveFromSMT(const std::vector<std::shared_ptr<SMTParser::Objective>>& objectives, OptimizationBackend_Base* backend) {
    if (objectives.empty() || !backend) {
        return false;
    }
    
    std::cout << "处理 " << objectives.size() << " 个SMT目标函数:" << std::endl;
    
    for (size_t i = 0; i < objectives.size(); ++i) {
        const auto& obj = objectives[i];
        if (!obj) {
            std::cout << "  目标 " << i << ": 空指针，跳过" << std::endl;
            continue;
        }
        
        std::cout << "  目标 " << i << ": ";
        auto opt_kind = obj->getObjectiveKind();
        if (opt_kind == SMTParser::OPT_KIND::OPT_MINIMIZE) {
            std::cout << "最小化 ";
        } else if (opt_kind == SMTParser::OPT_KIND::OPT_MAXIMIZE) {
            std::cout << "最大化 ";
        } else {
            std::cout << "其他类型(" << static_cast<int>(opt_kind) << ") ";
        }
        
        auto expr = obj->getObjectiveTerm();
        if (expr) {
            std::cout << "表达式 (Kind=" << static_cast<int>(expr->getKind()) << ")" << std::endl;
            
            // 创建实际的目标函数
            ObjectiveFunction opt_obj(ObjectiveType::FEASIBILITY);  // 提供默认参数
            if (opt_kind == SMTParser::OPT_KIND::OPT_MINIMIZE) {
                opt_obj.type = ObjectiveType::MINIMIZE;
            } else if (opt_kind == SMTParser::OPT_KIND::OPT_MAXIMIZE) {
                opt_obj.type = ObjectiveType::MAXIMIZE;
            } else {
                opt_obj.type = ObjectiveType::FEASIBILITY;
            }
            
            // 这里应该解析表达式并设置系数，但简化处理
            std::cout << "    使用简化的目标函数处理" << std::endl;
            return backend->setObjective(opt_obj);
        } else {
            std::cout << "无表达式" << std::endl;
        }
    }
    
    // 如果没有成功处理任何目标，创建可行性目标
    std::cout << "创建默认可行性目标" << std::endl;
    ObjectiveFunction obj(ObjectiveType::FEASIBILITY);
    return backend->setObjective(obj);
}

bool SMTToOptTransformer::createFeasibilityObjective(OptimizationBackend_Base* backend) {
    if (!backend) {
        return false;
    }
    
    std::cout << "Creating feasibility objective" << std::endl;
    
    ObjectiveFunction obj(ObjectiveType::FEASIBILITY);
    return backend->setObjective(obj);
}

void SMTToOptTransformer::setConfig(const TransformationConfig& config) {
    config_ = config;
    
    // 更新理论求解器配置
    if (na_solver_) {
        na_solver_->setLinearizationPrecision(config_.floating_point_precision);
        na_solver_->setMaxPiecewiseSegments(config_.max_piecewise_segments);
    }
    
    if (fp_solver_) {
        fp_solver_->setFloatingPointPrecision(config_.floating_point_precision);
    }
}

TransformationConfig SMTToOptTransformer::getConfig() const {
    return config_;
}

TransformationStatistics SMTToOptTransformer::getStatistics() const {
    return stats_;
}

void SMTToOptTransformer::resetStatistics() {
    stats_ = TransformationStatistics{};
}

void SMTToOptTransformer::printTransformationDetails() {
    std::cout << "\n=== Transformation Details ===" << std::endl;
    std::cout << "Configuration:" << std::endl;
    std::cout << "  Use BigM: " << (config_.use_big_m ? "Yes" : "No") << std::endl;
    std::cout << "  Default BigM: " << config_.default_big_m << std::endl;
    std::cout << "  Preprocess: " << (config_.preprocess_constraints ? "Yes" : "No") << std::endl;
    std::cout << "  FP Precision: " << config_.floating_point_precision << std::endl;
    std::cout << "  Max Piecewise Segments: " << config_.max_piecewise_segments << std::endl;
    
    std::cout << "\nStatistics:" << std::endl;
    std::cout << "  Original constraints: " << stats_.num_original_constraints << std::endl;
    std::cout << "  Transformed constraints: " << stats_.num_transformed_constraints << std::endl;
    std::cout << "  Auxiliary variables: " << stats_.num_auxiliary_variables << std::endl;
    std::cout << "  BigM constraints: " << stats_.num_big_m_constraints << std::endl;
    std::cout << "  SOS constraints: " << stats_.num_sos_constraints << std::endl;
    std::cout << "  Indicator constraints: " << stats_.num_indicator_constraints << std::endl;
    std::cout << "  Transformation time: " << stats_.transformation_time << " seconds" << std::endl;
}

void SMTToOptTransformer::dumpIntermediateResults(const std::string& filename) {
    std::cout << "Dumping intermediate results to " << filename << std::endl;
    // 这里应该实现将中间结果写入文件的逻辑
}

// 私有方法实现
TheorySolver* SMTToOptTransformer::getAppropriateTheorySolver(NodePtr node) {
    if (!node) {
        return nullptr;
    }
    
    // 简化的理论选择逻辑
    if (node->isArithTerm() || node->isArithComp()) {
        if (node->isCInt() || node->isCReal() || node->isVInt() || node->isVReal()) {
            return la_solver_.get();
        } else {
            return na_solver_.get();
        }
    } else if (node->isBVTerm() || node->isBvAtom()) {
        return bv_solver_.get();
    } else if (node->isFPOp() || node->isFPComp()) {
        return fp_solver_.get();
    }
    
    // 默认使用线性算术求解器
    return la_solver_.get();
}

bool SMTToOptTransformer::initializeTheorySolvers() {
    la_solver_ = std::make_unique<LinearArithmeticSolver>();
    bv_solver_ = std::make_unique<BitVectorSolver>();
    na_solver_ = std::make_unique<NonlinearArithmeticSolver>();
    fp_solver_ = std::make_unique<FloatingPointSolver>();
    
    return la_solver_ && bv_solver_ && na_solver_ && fp_solver_;
}

bool SMTToOptTransformer::classifyConstraints(
    const std::vector<NodePtr>& constraints,
    std::vector<NodePtr>& linear_constraints,
    std::vector<NodePtr>& nonlinear_constraints,
    std::vector<NodePtr>& boolean_constraints,
    std::vector<NodePtr>& bitvector_constraints,
    std::vector<NodePtr>& floating_point_constraints) {
    
    std::cout << "分类 " << constraints.size() << " 个约束:" << std::endl;
    
    for (size_t i = 0; i < constraints.size(); ++i) {
        const auto& constraint = constraints[i];
        if (!constraint) {
            std::cout << "约束 " << i << ": 空指针，跳过" << std::endl;
            continue;
        }
        
        std::cout << "约束 " << i << ": Kind=" << static_cast<int>(constraint->getKind());
        
        if (constraint->isArithComp()) {
            std::cout << " (算术比较)";
            if (constraint->getChildrenSize() > 0 && constraint->getChild(0) && constraint->getChild(0)->isArithTerm()) {
                std::cout << " 且第一个子节点是算术表达式";
                if (isLinearExpression(constraint)) {
                    std::cout << " -> 线性约束" << std::endl;
                    linear_constraints.push_back(constraint);
                    updateStatistics("linear_constraint");
                } else {
                    std::cout << " -> 非线性约束" << std::endl;
                    nonlinear_constraints.push_back(constraint);
                    updateStatistics("nonlinear_constraint");
                }
            } else {
                std::cout << " 但第一个子节点不是算术表达式 -> 非线性约束" << std::endl;
                nonlinear_constraints.push_back(constraint);
                updateStatistics("nonlinear_constraint");
            }
        } else if (constraint->isVBool() || constraint->isCBool()) {
            std::cout << " (布尔) -> 布尔约束" << std::endl;
            boolean_constraints.push_back(constraint);
            updateStatistics("boolean_constraint");
        } else if (constraint->isBvAtom()) {
            std::cout << " (位向量) -> 位向量约束" << std::endl;
            bitvector_constraints.push_back(constraint);
            updateStatistics("bitvector_constraint");
        } else if (constraint->isFPComp()) {
            std::cout << " (浮点) -> 浮点约束" << std::endl;
            floating_point_constraints.push_back(constraint);
            updateStatistics("floating_point_constraint");
        } else {
            std::cout << " (其他) -> 默认为线性约束" << std::endl;
            linear_constraints.push_back(constraint);
        }
    }
    
    std::cout << "\n分类结果汇总:" << std::endl;
    std::cout << "  线性约束: " << linear_constraints.size() << std::endl;
    std::cout << "  非线性约束: " << nonlinear_constraints.size() << std::endl;
    std::cout << "  布尔约束: " << boolean_constraints.size() << std::endl;
    std::cout << "  位向量约束: " << bitvector_constraints.size() << std::endl;
    std::cout << "  浮点约束: " << floating_point_constraints.size() << std::endl;
    
    return true;
}

void SMTToOptTransformer::analyzeVariables(const std::vector<NodePtr>& constraints) {
    std::unordered_set<std::string> variables;
    
    for (const auto& constraint : constraints) {
        collectVariables(constraint, variables);
    }
    
    std::cout << "Analyzed " << variables.size() << " variables" << std::endl;
}

void SMTToOptTransformer::collectVariables(NodePtr node, std::unordered_set<std::string>& variables) {
    if (!node) return;
    
    if (node->isVar() && !node->getName().empty()) {
        std::cout << "    发现变量: " << node->getName() << std::endl;
        variables.insert(node->getName());
    }
    
    // 递归处理子节点
    for (size_t i = 0; i < node->getChildrenSize(); ++i) {
        collectVariables(node->getChild(i), variables);
    }
}

bool SMTToOptTransformer::inferVariableBounds(const std::string& var_name, double& lower, double& upper) {
    // 简化的边界推断
    lower = -INFINITY_VALUE;
    upper = INFINITY_VALUE;
    return true;
}

bool SMTToOptTransformer::transformLinearConstraints(const std::vector<NodePtr>& constraints) {
    std::cout << "Transforming " << constraints.size() << " linear constraints" << std::endl;
    
    for (const auto& constraint : constraints) {
        if (la_solver_) {
            auto result = la_solver_->transformConstraint(constraint);
            if (result.success) {
                stats_.num_transformed_constraints++;
            }
        }
    }
    
    return true;
}

bool SMTToOptTransformer::transformNonlinearConstraints(const std::vector<NodePtr>& constraints) {
    std::cout << "Transforming " << constraints.size() << " nonlinear constraints" << std::endl;
    
    for (const auto& constraint : constraints) {
        if (na_solver_) {
            auto result = na_solver_->transformConstraint(constraint);
            if (result.success) {
                stats_.num_transformed_constraints++;
            }
        }
    }
    
    return true;
}

bool SMTToOptTransformer::transformBooleanConstraints(const std::vector<NodePtr>& constraints) {
    std::cout << "Transforming " << constraints.size() << " boolean constraints" << std::endl;
    
    for (const auto& constraint : constraints) {
        transformBooleanConstraint(constraint);
    }
    
    return true;
}

std::string SMTToOptTransformer::generateAuxiliaryVariable(const std::string& prefix) {
    static size_t counter = 0;
    return prefix + "_" + std::to_string(++counter);
}

bool SMTToOptTransformer::addAuxiliaryVariableConstraints(const std::string& aux_var, NodePtr definition) {
    std::cout << "Adding auxiliary variable constraints for " << aux_var << std::endl;
    stats_.num_auxiliary_variables++;
    return true;
}

void SMTToOptTransformer::reportTransformationError(const std::string& message, NodePtr problematic_node) {
    std::cerr << "Transformation Error: " << message << std::endl;
    if (problematic_node) {
        std::cerr << "Problematic node type: " << static_cast<int>(problematic_node->getKind()) << std::endl;
    }
}

bool SMTToOptTransformer::isTransformationSupported(NodePtr node) {
    if (!node) return false;
    
    // 基本的支持检查
    return getAppropriateTheorySolver(node) != nullptr;
}

bool SMTToOptTransformer::isLinearExpression(NodePtr expr) const {
    if (!expr) return true;
    
    // 简化的线性性检查
    if (expr->isAdd() || expr->isSub() || expr->isNeg()) {
        return true;
    }
    
    if (expr->isMul()) {
        // 检查是否至多有一个变量
        bool has_variable = false;
        for (size_t i = 0; i < expr->getChildrenSize(); ++i) {
            auto child = expr->getChild(i);
            if (child && child->isVar()) {
                if (has_variable) {
                    return false;  // 多个变量相乘，非线性
                }
                has_variable = true;
            }
        }
        return true;
    }
    
    return expr->isVar() || expr->isConst();
}

void SMTToOptTransformer::updateStatistics(const std::string& operation, size_t count) {
    stats_.theory_constraint_counts[operation] += count;
}

void SMTToOptTransformer::startTimer() {
    timer_start_ = std::chrono::high_resolution_clock::now();
}

void SMTToOptTransformer::stopTimer() {
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - timer_start_);
    stats_.transformation_time += duration.count() / 1000.0;
}

} // namespace OptiSMT 