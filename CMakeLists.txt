cmake_minimum_required(VERSION 3.12)
project(OptiSMT VERSION 1.0.0 LANGUAGES CXX)

# 设置C++标准
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 设置构建类型
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

# 编译选项
set(CMAKE_CXX_FLAGS_DEBUG "-g -O0 -Wall -Wextra")
set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG")

# 添加SMTParser子模块
add_subdirectory(SMTParser)

# 包含目录
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/src)
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/SMTParser/include)

# OptiSMT源文件
set(OPTISMT_SOURCES
    src/smt_transformer.cpp
    src/smt_transformer.h
    src/common.h
)

# 创建OptiSMT库
add_library(optismt_lib ${OPTISMT_SOURCES})

# 链接SMTParser
target_link_libraries(optismt_lib smtparser)

# 创建主程序
add_executable(optismt src/main.cpp)
target_link_libraries(optismt optismt_lib)

# 安装规则
install(TARGETS optismt
    RUNTIME DESTINATION bin
)

install(TARGETS optismt_lib
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
)

install(DIRECTORY src/
    DESTINATION include/optismt
    FILES_MATCHING PATTERN "*.h"
)

# 显示配置摘要
message(STATUS "")
message(STATUS "OptiSMT Configuration Summary:")
message(STATUS "  Version: ${PROJECT_VERSION}")
message(STATUS "  Build type: ${CMAKE_BUILD_TYPE}")
message(STATUS "  C++ standard: ${CMAKE_CXX_STANDARD}")
message(STATUS "  Install prefix: ${CMAKE_INSTALL_PREFIX}")
message(STATUS "")
message(STATUS "OptiSMT是一个简洁的SMT到线性程序转换器")
message(STATUS "使用大M方法处理OR约束，生成LP/MPS文件")
message(STATUS "") 