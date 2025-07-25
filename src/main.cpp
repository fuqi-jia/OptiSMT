#include "smt_transformer.h"
#include <iostream>
#include <string>

using namespace OptiSMT;

void printUsage(const char* program_name) {
    std::cout << "OptiSMT - SMT到线性程序转换器\n"
              << "使用大M方法处理OR约束，生成LP/MPS文件\n\n"
              << "用法: " << program_name << " [选项] <SMT文件>\n\n"
              << "选项:\n"
              << "  -h, --help           显示此帮助信息\n"
              << "  -m, --big-m <值>     设置大M值 (默认: " << DEFAULT_BIG_M << ")\n"
              << "  -o, --output <文件>  输出文件前缀 (默认: output)\n"
              << "  --lp-only           只生成LP文件\n"
              << "  --mps-only          只生成MPS文件\n"
              << "  -v, --verbose       详细输出\n\n"
              << "示例:\n"
              << "  " << program_name << " problem.smt2\n"
              << "  " << program_name << " -m 10000 -o result problem.smt2\n"
              << "  " << program_name << " --lp-only problem.smt2\n\n";
}

int main(int argc, char* argv[]) {
    // 默认配置
    double big_m = DEFAULT_BIG_M;
    std::string input_file;
    std::string output_prefix = "output";
    bool verbose = false;
    bool lp_only = false;
    bool mps_only = false;
    
    // 解析命令行参数
    for (int i = 1; i < argc; ++i) {
        std::string arg(argv[i]);
        
        if (arg == "-h" || arg == "--help") {
            printUsage(argv[0]);
            return 0;
        }
        else if (arg == "-m" || arg == "--big-m") {
            if (i + 1 >= argc) {
                std::cerr << "错误：--big-m 需要一个数值参数\n";
                return 1;
            }
            big_m = std::stod(argv[++i]);
        }
        else if (arg == "-o" || arg == "--output") {
            if (i + 1 >= argc) {
                std::cerr << "错误：--output 需要一个文件名参数\n";
                return 1;
            }
            output_prefix = argv[++i];
        }
        else if (arg == "--lp-only") {
            lp_only = true;
        }
        else if (arg == "--mps-only") {
            mps_only = true;
        }
        else if (arg == "-v" || arg == "--verbose") {
            verbose = true;
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
        std::cerr << "错误：必须指定输入的SMT文件\n";
        printUsage(argv[0]);
        return 1;
    }
    
    if (lp_only && mps_only) {
        std::cerr << "错误：不能同时指定 --lp-only 和 --mps-only\n";
        return 1;
    }
    
    try {
        std::cout << "=== OptiSMT: SMT到线性程序转换器 ===\n" << std::endl;
        
        // 创建转换器
        SMTTransformer transformer;
        transformer.setBigM(big_m);
        
        if (verbose) {
            std::cout << "配置信息:\n";
            std::cout << "  输入文件: " << input_file << "\n";
            std::cout << "  输出前缀: " << output_prefix << "\n";
            std::cout << "  大M值: " << big_m << "\n";
            std::cout << std::endl;
        }
        
        // 解析和转换SMT文件
        std::cout << "步骤1: 解析SMT文件..." << std::endl;
        if (!transformer.transformSMTFile(input_file)) {
            std::cerr << "错误：SMT文件解析失败\n";
            return 1;
        }
        
        // 应用大M方法处理OR约束
        std::cout << "\n步骤2: 应用大M方法转换OR约束..." << std::endl;
        transformer.applyBigMTransformation();
        
        // 生成LP/MPS文件
        std::cout << "\n步骤3: 生成线性程序文件..." << std::endl;
        
        bool success = true;
        
        if (!mps_only) {
            std::string lp_file = output_prefix + ".lp";
            if (!transformer.generateLPFile(lp_file)) {
                std::cerr << "警告：LP文件生成失败\n";
                success = false;
            }
        }
        
        if (!lp_only) {
            std::string mps_file = output_prefix + ".mps";
            if (!transformer.generateMPSFile(mps_file)) {
                std::cerr << "警告：MPS文件生成失败\n";
                success = false;
            }
        }
        
        // 显示统计信息
        if (verbose) {
            transformer.printStatistics();
        }
        
        if (success) {
            std::cout << "\n=== 转换完成 ===\n";
            std::cout << "已生成以下文件:\n";
            if (!mps_only) {
                std::cout << "  " << output_prefix << ".lp (LP格式)\n";
            }
            if (!lp_only) {
                std::cout << "  " << output_prefix << ".mps (MPS格式)\n";
            }
            std::cout << "\n可以使用商业求解器(如Gurobi、CPLEX)或开源求解器(如SCIP)求解这些文件。\n";
            return 0;
        } else {
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
