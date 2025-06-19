#include "optismt.h"
#include <iostream>
#include <string>
#include <chrono>

using namespace OptiSMT;

void printUsage(const char* program_name) {
    std::cout << "用法: " << program_name << " [选项] <SMT文件>\n"
              << "\n选项:\n"
              << "  -h, --help                    显示此帮助信息\n"
              << "  -b, --backend <backend>       选择优化后端 (gurobi|cplex|z3|scip)\n"
              << "  -t, --time-limit <seconds>    设置时间限制\n"
              << "  -g, --mip-gap <gap>          设置MIP求解间隙\n"
              << "  -m, --big-m <value>          设置BigM值\n"
              << "  --no-big-m                   禁用BigM方法\n"
              << "  --no-preprocess              禁用预处理\n"
              << "  -v, --verbose                详细输出\n"
              << "  -s, --statistics             显示统计信息\n"
              << "  --dump-model <file>          导出优化模型到文件\n"
              << "\n支持的后端:\n"
              << "  gurobi   - Gurobi优化器 (默认)\n"
              << "  cplex    - IBM CPLEX优化器\n"
              << "  z3       - Z3优化器\n"
              << "  scip     - SCIP优化器\n"
              << "\n示例:\n"
              << "  " << program_name << " problem.smt2\n"
              << "  " << program_name << " -b gurobi -t 300 problem.smt2\n"
              << "  " << program_name << " --dump-model model.lp problem.smt2\n";
}

OptimizationBackend parseBackend(const std::string& backend_str) {
    if (backend_str == "gurobi") return OptimizationBackend::GUROBI;
    if (backend_str == "cplex") return OptimizationBackend::CPLEX;
    if (backend_str == "z3") return OptimizationBackend::Z3_OPTIMIZE;
    if (backend_str == "scip") return OptimizationBackend::SCIP;
    
    std::cerr << "错误：未知的后端 '" << backend_str << "'\n";
    return OptimizationBackend::GUROBI;
}

std::string resultToString(SolverResult result) {
    switch (result) {
        case SolverResult::SAT: return "SAT";
        case SolverResult::UNSAT: return "UNSAT";
        case SolverResult::UNKNOWN: return "UNKNOWN";
        case SolverResult::ERROR: return "ERROR";
        default: return "UNKNOWN";
    }
}

int main(int argc, char* argv[]) {
    // 默认配置
    OptimizationBackend backend = OptimizationBackend::GUROBI;
    double time_limit = -1.0;  // 无限制
    double mip_gap = -1.0;     // 使用默认值
    double big_m = DEFAULT_BIG_M;
    bool use_big_m = true;
    bool preprocess = true;
    bool verbose = false;
    bool show_statistics = false;
    std::string model_dump_file;
    std::string input_file;
    
    // 解析命令行参数
    for (int i = 1; i < argc; ++i) {
        std::string arg(argv[i]);
        
        if (arg == "-h" || arg == "--help") {
            printUsage(argv[0]);
            return 0;
        }
        else if (arg == "-b" || arg == "--backend") {
            if (i + 1 >= argc) {
                std::cerr << "错误：--backend 需要一个参数\n";
                return 1;
            }
            backend = parseBackend(argv[++i]);
        }
        else if (arg == "-t" || arg == "--time-limit") {
            if (i + 1 >= argc) {
                std::cerr << "错误：--time-limit 需要一个参数\n";
                return 1;
            }
            time_limit = std::stod(argv[++i]);
        }
        else if (arg == "-g" || arg == "--mip-gap") {
            if (i + 1 >= argc) {
                std::cerr << "错误：--mip-gap 需要一个参数\n";
                return 1;
            }
            mip_gap = std::stod(argv[++i]);
        }
        else if (arg == "-m" || arg == "--big-m") {
            if (i + 1 >= argc) {
                std::cerr << "错误：--big-m 需要一个参数\n";
                return 1;
            }
            big_m = std::stod(argv[++i]);
        }
        else if (arg == "--no-big-m") {
            use_big_m = false;
        }
        else if (arg == "--no-preprocess") {
            preprocess = false;
        }
        else if (arg == "-v" || arg == "--verbose") {
            verbose = true;
        }
        else if (arg == "-s" || arg == "--statistics") {
            show_statistics = true;
        }
        else if (arg == "--dump-model") {
            if (i + 1 >= argc) {
                std::cerr << "错误：--dump-model 需要一个参数\n";
                return 1;
            }
            model_dump_file = argv[++i];
        }
        else if (arg[0] != '-') {
            if (input_file.empty()) {
                input_file = arg;
            } else {
                std::cerr << "错误：只能指定一个输入文件\n";
                return 1;
            }
        }
        else {
            std::cerr << "错误：未知选项 '" << arg << "'\n";
            printUsage(argv[0]);
            return 1;
        }
    }
    
    if (input_file.empty()) {
        std::cerr << "错误：必须指定输入文件\n";
        printUsage(argv[0]);
        return 1;
    }
    
    try {
        // 创建求解器
        if (verbose) {
            std::cout << "创建OptiSMT求解器..." << std::endl;
        }
        
        auto solver = createOptiSMTSolver(backend);
        
        // 配置求解器
        solver->setUseBigM(use_big_m);
        solver->setDefaultBigM(big_m);
        solver->setPreprocessConstraints(preprocess);
        
        if (time_limit > 0) {
            solver->setTimeLimit(time_limit);
        }
        
        if (mip_gap > 0) {
            solver->setMIPGap(mip_gap);
        }
        
        // 加载SMT文件
        if (verbose) {
            std::cout << "加载SMT文件: " << input_file << std::endl;
        }
        
        if (!solver->loadSMTFile(input_file)) {
            std::cerr << "错误：无法加载SMT文件 '" << input_file << "'\n";
            return 1;
        }
        
        // 导出模型（如果请求）
        if (!model_dump_file.empty()) {
            if (verbose) {
                std::cout << "导出优化模型到: " << model_dump_file << std::endl;
            }
            solver->dumpOptimizationModel(model_dump_file);
        }
        
        // 求解
        if (verbose) {
            std::cout << "开始求解..." << std::endl;
        }
        
        auto start_time = std::chrono::high_resolution_clock::now();
        SolverResult result = solver->solve();
        auto end_time = std::chrono::high_resolution_clock::now();
        
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);
        
        // 输出结果
        std::cout << resultToString(result) << std::endl;
        
        if (verbose) {
            std::cout << "求解时间: " << duration.count() << " ms" << std::endl;
        }
        
        // 如果有解，输出模型
        if (result == SolverResult::SAT) {
            std::unordered_map<std::string, double> model;
            if (solver->getModel(model) && verbose) {
                std::cout << "\n模型:" << std::endl;
                for (const auto& [var, value] : model) {
                    std::cout << "  " << var << " = " << value << std::endl;
                }
            }
            
            // 输出目标值（如果有）
            double obj_value;
            if (solver->getObjectiveValue(obj_value)) {
                std::cout << "目标值: " << obj_value << std::endl;
            }
        }
        
        // 显示统计信息
        if (show_statistics) {
            std::cout << "\n=== 求解统计 ===" << std::endl;
            solver->printStatistics();
            
            std::cout << "\n=== 转换统计 ===" << std::endl;
            solver->printTransformationStatistics();
        }
        
        // 返回适当的退出码
        switch (result) {
            case SolverResult::SAT:
                return 10;  // SAT的标准退出码
            case SolverResult::UNSAT:
                return 20;  // UNSAT的标准退出码
            case SolverResult::UNKNOWN:
                return 0;
            case SolverResult::ERROR:
                return 1;
            default:
                return 1;
        }
        
    } catch (const std::exception& e) {
        std::cerr << "错误：" << e.what() << std::endl;
        return 1;
    } catch (...) {
        std::cerr << "未知错误" << std::endl;
        return 1;
    }
}

// 版本信息函数
void printVersion() {
    std::cout << "OptiSMT 版本 1.0.0\n"
              << "SMT问题到优化问题转换求解器\n"
              << "作者：OptiSMT开发团队\n"
              << "支持的理论：线性算术、位向量、非线性算术、浮点数\n"
              << "支持的后端：Gurobi、CPLEX、Z3、SCIP\n";
}
