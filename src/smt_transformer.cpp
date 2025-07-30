#include "smt_transformer.h"
#include <fstream>
#include <iostream>
#include <cassert>
#define epsilon 1e-8

namespace OptiSMT {

bool SMTTransformer::transformSMTFile(const std::string& filename) {
    std::cout << "正在解析SMT文件: " << filename << std::endl;
    
    // 创建parser并解析文件
    auto parser = SMTParser::newParser();
    parser->setOption("keep_let", false);
    
    if (!parser->parse(filename)) {
        std::cerr << "错误：无法解析SMT文件" << std::endl;
        return false;
    }
    
    return transformSMTConstraints(parser);
}

bool SMTTransformer::transformSMTConstraints(ParserPtr parser) {
    // 清空之前的结果
    variables_.clear();
    linear_constraints_.clear();
    or_constraints_.clear();
    var_map_.clear();
    aux_var_counter_ = 0;
    
    // 获取变量
    auto smt_variables = parser->getVariables();
    std::cout << "发现 " << smt_variables.size() << " 个变量" << std::endl;
    
    // 添加变量
    for (auto var : smt_variables) {
        if (!var) continue;
        
        VariableType type = VariableType::REAL;
        if (var->isVInt()) {
            type = VariableType::INTEGER;
        } else if (var->isVBool()) {
            type = VariableType::BINARY;
        }
        
        addVariable(var->getName(), type);
    }
    
    // 获取约束
    auto assertions = parser->getAssertions();
    std::cout << "发现 " << assertions.size() << " 个约束" << std::endl;
    
    // 处理每个约束
    for (auto assertion : assertions) {
        if (!assertion) continue;
        
        if (!processNode(assertion)) {
            std::cerr << "警告：无法处理某个约束" << std::endl;
        }
    }
    
    std::cout << "转换完成：" << std::endl;
    std::cout << "  变量数量: " << variables_.size() << std::endl;
    std::cout << "  线性约束: " << linear_constraints_.size() << std::endl;
    std::cout << "  OR约束: " << or_constraints_.size() << std::endl;
    
    return true;
}

bool SMTTransformer::processNode(NodePtr node) {
    if (!node) return false;
    
    // 处理OR节点
    if (node->isOr()) {
        return processOrNode(node);
    }
    
    // 处理AND节点 - 递归处理子节点
    if (node->isAnd()) {
        bool success = true;
        for (size_t i = 0; i < node->getChildrenSize(); ++i) {
            success &= processNode(node->getChild(i));
        }
        return success;
    }
    
    // 处理线性约束
    return processLinearConstraint(node);
}

bool SMTTransformer::processOrNode(NodePtr node) {
    std::cout << "处理OR约束，子句数量: " << node->getChildrenSize() << std::endl;
    
    OrConstraint or_constraint;
    
    // 处理每个子句
    for (size_t i = 0; i < node->getChildrenSize(); ++i) {
        auto child = node->getChild(i);
        
        std::vector<LinearTerm> terms;
        SMTParser::Number constant = 0.0;
        
        if (!extractLinearTerms(child, terms, constant)) {
            std::cerr << "警告：无法提取线性项从OR子句" << std::endl;
            continue;
        }
        
        ConstraintType type = getConstraintType(child);
        LinearConstraint constraint(type, -constant);
        
        for (const auto& term : terms) {
            constraint.addTerm(term.coefficient, term.variable);
        }
        
        or_constraint.addClause(constraint);
    }
    
    or_constraints_.push_back(or_constraint);
    return true;
}

bool SMTTransformer::processLinearConstraint(NodePtr node) {
    std::vector<LinearTerm> terms;
    SMTParser::Number constant = 0.0;
    
    if (!extractLinearTerms(node, terms, constant)) {
        return false;
    }
    
    ConstraintType type = getConstraintType(node);
    addLinearConstraint(terms, type, -constant);
    
    return true;
}

bool SMTTransformer::extractLinearTerms(NodePtr node, std::vector<LinearTerm>& terms, SMTParser::Number& constant) {
    if (!node) return false;
    
    auto kind = node->getKind();
    
    // 处理比较操作
    if (node->isLe() || node->isGe() || node->isEq() || node->isLt() || node->isGt()){
        
        if (node->getChildrenSize() != 2) return false;
        
        auto left = node->getChild(0);
        auto right = node->getChild(1);
        
        // 提取左侧
        std::vector<LinearTerm> left_terms;
        SMTParser::Number left_constant = 0.0;
        if (!extractLinearExpression(left, left_terms, left_constant)) {
            return false;
        }
        
        // 提取右侧
        std::vector<LinearTerm> right_terms;
        SMTParser::Number right_constant = 0.0;
        if (!extractLinearExpression(right, right_terms, right_constant)) {
            return false;
        }
        
            // left <= right -> left - right <= 0
            // 移动到左侧: left - right <= 0
        terms = left_terms;
        for (const auto& term : right_terms) {
            terms.emplace_back(-term.coefficient, term.variable);
        }
        constant = left_constant - right_constant;
        if(node->isLt()){
            constant = constant + epsilon;
        }
        if(node->isGt()){
            constant = constant - epsilon;
        }
        else assert(false);
        return true;
    }
    
    return false;
}

bool SMTTransformer::extractLinearExpression(NodePtr node, std::vector<LinearTerm>& terms, SMTParser::Number& constant) {
    if (!node) return false;
    
    // 常数
    if (node->isCInt()) {
        constant += node->getValue()->getNumberValue();
        return true;
    }
    
    if (node->isCReal()) {
        constant += node->getValue()->getNumberValue();
        return true;
    }
    
    // 变量
    if (node->isVar()) {
        terms.emplace_back(1.0, node->getName());
        return true;
    }
    
    // 一元负号
    if (node->isNeg()) {
        if (node->getChildrenSize() != 1) {
            return false;
        }
        
        std::vector<LinearTerm> neg_terms;
        SMTParser::Number neg_constant = 0.0;
        if (!extractLinearExpression(node->getChild(0), neg_terms, neg_constant)) {
            return false;
        }
        
        // 添加负号的项
        for (const auto& term : neg_terms) {
            terms.emplace_back(-term.coefficient, term.variable);
        }
        constant -= neg_constant;
        return true;
    }
    
    // 加法
    if (node->isAdd()) {
        for (size_t i = 0; i < node->getChildrenSize(); ++i) {
            if (!extractLinearExpression(node->getChild(i), terms, constant)) {
                return false;
            }
        }
        return true;
    }
    
    // 减法
    if (node->isSub()) {
        if (node->getChildrenSize() == 1) {
            // 一元负号
            std::vector<LinearTerm> sub_terms;
            SMTParser::Number sub_constant = 0.0;
            if (!extractLinearExpression(node->getChild(0), sub_terms, sub_constant)) {
                return false;
            }
            for (const auto& term : sub_terms) {
                terms.emplace_back(-term.coefficient, term.variable);
            }
            constant -= sub_constant;
            return true;
        } else if (node->getChildrenSize() == 2) {
            // 二元减法
            if (!extractLinearExpression(node->getChild(0), terms, constant)) {
                return false;
            }
            std::vector<LinearTerm> sub_terms;
            SMTParser::Number sub_constant = 0.0;
            if (!extractLinearExpression(node->getChild(1), sub_terms, sub_constant)) {
                return false;
            }
            for (const auto& term : sub_terms) {
                terms.emplace_back(-term.coefficient, term.variable);
            }
            constant -= sub_constant;
            return true;
        }
    }
    
    // 乘法（仅支持常数 * 变量）
    if (node->isMul()) {
        if (node->getChildrenSize() != 2) {
            return false;
        }
        
        auto left = node->getChild(0);
        auto right = node->getChild(1);
        
        // 尝试 常数 * 变量
        if ((left->isCInt() || 
             left->isCReal()) && 
             right->isVar()) {
            
            SMTParser::Number coeff = left->isCInt() ? 
                          left->getValue()->getNumberValue() : left->getValue()->getNumberValue();
            terms.emplace_back(coeff, right->getName());
            return true;
        }
        
        // 尝试 变量 * 常数
        if ((right->isCInt() || 
             right->isCReal()) && 
             left->isVar()) {
            
            SMTParser::Number coeff = right->isCInt() ? 
                          right->getValue()->getNumberValue() : right->getValue()->getNumberValue();
            terms.emplace_back(coeff, left->getName());
            return true;
        }
    }
    
    return false;
}

ConstraintType SMTTransformer::getConstraintType(NodePtr node) {
    if (!node) return ConstraintType::LINEAR_EQ;
    
    auto kind = node->getKind();
    switch (kind) {
        case SMTParser::NODE_KIND::NT_LE: return ConstraintType::LINEAR_LE;
        case SMTParser::NODE_KIND::NT_LT: return ConstraintType::LINEAR_LE; // 转换为 <=
        case SMTParser::NODE_KIND::NT_GE: return ConstraintType::LINEAR_GE;
        case SMTParser::NODE_KIND::NT_GT: return ConstraintType::LINEAR_GE; // 转换为 >=
        case SMTParser::NODE_KIND::NT_EQ: return ConstraintType::LINEAR_EQ;
        default: return ConstraintType::LINEAR_EQ;
    }
}

std::string SMTTransformer::addVariable(const std::string& name, VariableType type) {
    if (var_map_.find(name) != var_map_.end()) {
        return name; // 已存在
    }
    
    var_map_[name] = variables_.size();
    variables_.emplace_back(name, type);
    
    return name;
}

std::string SMTTransformer::generateAuxVariable() {
    return "aux_" + std::to_string(aux_var_counter_++);
}

void SMTTransformer::addLinearConstraint(const std::vector<LinearTerm>& terms, ConstraintType type, SMTParser::Number rhs) {
    LinearConstraint constraint(type, rhs);
    for (const auto& term : terms) {
        constraint.addTerm(term.coefficient, term.variable);
    }
    linear_constraints_.push_back(constraint);
}

void SMTTransformer::applyBigMTransformation() {
    std::cout << "应用BigM方法转换 " << or_constraints_.size() << " 个OR约束" << std::endl;
    
    for (const auto& or_constraint : or_constraints_) {
        transformOrConstraint(or_constraint);
    }
    
    or_constraints_.clear(); // 清空OR约束，因为已经转换为线性约束
    
    std::cout << "BigM转换完成，现有线性约束数量: " << linear_constraints_.size() << std::endl;
}

void SMTTransformer::transformOrConstraint(const OrConstraint& or_constraint) {
    // 为每个子句创建二进制指示变量
    std::vector<std::string> indicator_vars;
    
    for (size_t i = 0; i < or_constraint.clauses.size(); ++i) {
        std::string ind_var = generateAuxVariable();
        addVariable(ind_var, VariableType::BINARY);
        indicator_vars.push_back(ind_var);
    }
    
    // 确保至少一个指示变量为1：sum(indicator_vars) >= 1
    LinearConstraint sum_constraint(ConstraintType::LINEAR_GE, 1.0);
    for (const auto& ind_var : indicator_vars) {
        sum_constraint.addTerm(1.0, ind_var);
    }
    linear_constraints_.push_back(sum_constraint);
    
    // 为每个子句添加BigM约束
    for (size_t i = 0; i < or_constraint.clauses.size(); ++i) {
        const auto& clause = or_constraint.clauses[i];
        const std::string& ind_var = indicator_vars[i];
        
        // BigM: Ax>=B -> Ax+M*(1-indicator)>=B -> Ax-M*indicator>=B-M
        // Ax<=B -> Ax-M*(1-indicator)<=B -> Ax+M*indicator<=B+M

        int flag = (clause.type==OptiSMT::ConstraintType::LINEAR_LE)? 1 : -1;
        
        LinearConstraint big_m_constraint(clause.type, clause.rhs + flag * big_m_value_);
        
        // 添加原约束的项
        for (const auto& term : clause.terms) {
            big_m_constraint.addTerm(term.coefficient, term.variable);
        }
        
        // 添加BigM项
        big_m_constraint.addTerm(flag * big_m_value_, ind_var);
        
        linear_constraints_.push_back(big_m_constraint);
    }
}

void SMTTransformer::printStatistics() const {
    std::cout << "\n=== 转换统计 ===" << std::endl;
    std::cout << "变量总数: " << variables_.size() << std::endl;
    
    size_t real_vars = 0, int_vars = 0, bin_vars = 0;
    for (const auto& var : variables_) {
        switch (var.type) {
            case VariableType::REAL: real_vars++; break;
            case VariableType::INTEGER: int_vars++; break;
            case VariableType::BINARY: bin_vars++; break;
        }
    }
    
    std::cout << "  实数变量: " << real_vars << std::endl;
    std::cout << "  整数变量: " << int_vars << std::endl;
    std::cout << "  二进制变量: " << bin_vars << std::endl;
    
    std::cout << "约束总数: " << linear_constraints_.size() << std::endl;
    
    size_t eq_constraints = 0, le_constraints = 0, ge_constraints = 0;
    for (const auto& constraint : linear_constraints_) {
        switch (constraint.type) {
            case ConstraintType::LINEAR_EQ: eq_constraints++; break;
            case ConstraintType::LINEAR_LE: le_constraints++; break;
            case ConstraintType::LINEAR_GE: ge_constraints++; break;
            default: break;
        }
    }
    
    std::cout << "  等式约束: " << eq_constraints << std::endl;
    std::cout << "  <= 约束: " << le_constraints << std::endl;
    std::cout << ">= 约束: " << ge_constraints << std::endl;
    std::cout << "BigM值: " << big_m_value_ << std::endl;
}

bool SMTTransformer::generateLPFile(const std::string& filename) const {
    std::ofstream file(filename);
    if (!file.is_open()) {
        std::cerr << "错误：无法创建LP文件 " << filename << std::endl;
        return false;
    }
    
    std::cout << "生成LP文件: " << filename << std::endl;
    
    // LP文件头部
    file << "\\* SMT到LP转换生成的线性程序 *\\\n\n";
    
    // 目标函数（可行性问题，使用简单的目标函数）
    file << "Minimize\n";
    file << "obj: 0\n\n";
    
    // 约束部分
    file << "Subject To\n";
    
    for (size_t i = 0; i < linear_constraints_.size(); ++i) {
        file << "c" << i << ": " << formatLinearConstraint(linear_constraints_[i]) << "\n";
    }
    
    file << "\n";
    
    // 变量边界
    file << "Bounds\n";
    for (const auto& var : variables_) {
        file << formatVariable(var) << "\n";
    }
    
    file << "\n";
    
    // 整数变量声明
    std::vector<std::string> int_vars, bin_vars;
    for (const auto& var : variables_) {
        if (var.type == VariableType::INTEGER) {
            int_vars.push_back(var.name);
        } else if (var.type == VariableType::BINARY) {
            bin_vars.push_back(var.name);
        }
    }
    
    if (!int_vars.empty()) {
        file << "General\n";
        for (const auto& var : int_vars) {
            file << var << "\n";
        }
        file << "\n";
    }
    
    if (!bin_vars.empty()) {
        file << "Binary\n";
        for (const auto& var : bin_vars) {
            file << var << "\n";
        }
        file << "\n";
    }
    
    file << "End\n";
    file.close();
    
    std::cout << "LP文件生成完成" << std::endl;
    return true;
}

bool SMTTransformer::generateMPSFile(const std::string& filename) const {
    std::ofstream file(filename);
    if (!file.is_open()) {
        std::cerr << "错误：无法创建MPS文件 " << filename << std::endl;
        return false;
    }
    
    std::cout << "生成MPS文件: " << filename << std::endl;
    
    // MPS文件格式
    file << "NAME          SMT2LP\n";
    
    // ROWS部分
    file << "ROWS\n";
    file << " N  OBJ\n";  // 目标函数
    
    for (size_t i = 0; i < linear_constraints_.size(); ++i) {
        const auto& constraint = linear_constraints_[i];
        char row_type;
        switch (constraint.type) {
            case ConstraintType::LINEAR_EQ: row_type = 'E'; break;
            case ConstraintType::LINEAR_LE: row_type = 'L'; break;
            case ConstraintType::LINEAR_GE: row_type = 'G'; break;
            default: row_type = 'E'; break;
        }
        file << " " << row_type << "  C" << i << "\n";
    }
    
    // COLUMNS部分
    file << "COLUMNS\n";
    
    // 为每个变量生成列
    for (const auto& var : variables_) {
        // 目标函数系数（0表示可行性问题）
        // 整数/二进制标记
        if (var.type == VariableType::INTEGER || var.type == VariableType::BINARY) {
            file << "    MARK0001  'MARKER'                 'INTORG'\n";
            file << "    " << var.name << "  OBJ       0\n";
            file << "    MARK0001  'MARKER'                 'INTEND'\n";
        }
        
        // 约束系数
        for (size_t i = 0; i < linear_constraints_.size(); ++i) {
            const auto& constraint = linear_constraints_[i];
            
            SMTParser::Number coeff = 0.0;
            for (const auto& term : constraint.terms) {
                if (term.variable == var.name) {
                    coeff = term.coefficient;
                    break;
                }
            }
            
            if (coeff.abs() > 1e-10) {  // 非零系数
                file << "    " << var.name << "  C" << i << "       " << coeff.toString() << "\n";
            }
        }
        
    }
    
    // RHS部分
    file << "RHS\n";
    for (size_t i = 0; i < linear_constraints_.size(); ++i) {
        const auto& constraint = linear_constraints_[i];
        file << "    RHS1      C" << i << "       " << constraint.rhs.toString() << "\n";
    }
    
    // BOUNDS部分
    file << "BOUNDS\n";
    for (const auto& var : variables_) {
        if (var.type == VariableType::BINARY) {
            file << " BV BOUND1    " << var.name << "\n";
        } else {
            if (var.lower_bound > -1e20) {
                file << " LO BOUND1    " << var.name << "       " << var.lower_bound << "\n";
            }
            if (var.upper_bound < 1e20) {
                file << " UP BOUND1    " << var.name << "       " << var.upper_bound << "\n";
            }
            if (var.type == VariableType::INTEGER) {
                file << " MI BOUND1    " << var.name << "\n";  // 整数标记
            }
        }
    }
    
    file << "ENDATA\n";
    file.close();
    
    std::cout << "MPS文件生成完成" << std::endl;
    return true;
}

std::string SMTTransformer::formatLinearConstraint(const LinearConstraint& constraint) const {
    std::ostringstream oss;
    
    bool first = true;
    for (const auto& term : constraint.terms) {
        if (!first) {
            if (term.coefficient >= 0) {
                oss << " + ";
            } else {
                oss << " - ";
                oss << term.coefficient.abs().toString() << " " << term.variable;
                continue;
            }
        } else {
            if (term.coefficient < 0) {
                oss << "- ";
                oss << term.coefficient.abs().toString() << " " << term.variable;
                first = false;
                continue;
            }
        }
        
        if (term.coefficient.abs() < 1 + 1e-10) {
            oss << term.variable;
        } else {
            oss << term.coefficient.toString() << " " << term.variable;
        }
        first = false;
    }
    
    // 约束类型和右端值
    switch (constraint.type) {
        case ConstraintType::LINEAR_EQ:
            oss << " = " << constraint.rhs.toString();
            break;
        case ConstraintType::LINEAR_LE:
            oss << " <= " << constraint.rhs.toString();
            break;
        case ConstraintType::LINEAR_GE:
            oss << " >= " << constraint.rhs.toString();
            break;
    }
    
    return oss.str();
}

std::string SMTTransformer::formatVariable(const Variable& var) const {
    std::ostringstream oss;
    
    if (var.type == VariableType::BINARY) {
        oss << "0 <= " << var.name << " <= 1";
    } else {
        if (var.lower_bound > -1e20 && var.upper_bound < 1e20) {
            oss << var.lower_bound << " <= " << var.name << " <= " << var.upper_bound;
        } else if (var.lower_bound > -1e20) {
            oss << var.name << " >= " << var.lower_bound;
        } else if (var.upper_bound < 1e20) {
            oss << var.name << " <= " << var.upper_bound;
        } else {
            oss << var.name << " free";
        }
    }
    
    return oss.str();
}

} // namespace OptiSMT 