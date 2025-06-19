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

# 查找依赖包
find_package(PkgConfig REQUIRED)

# 添加SMTParser子模块
add_subdirectory(SMTParser)

# 包含目录
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/src)
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/SMTParser/include)

# 收集OptiSMT源文件
file(GLOB_RECURSE OPTISMT_SOURCES 
    "src/*.cpp"
    "src/*.h"
)

# 排除main.cpp，因为我们要单独处理
list(REMOVE_ITEM OPTISMT_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/main.cpp")

# 创建OptiSMT库
add_library(optismt_lib ${OPTISMT_SOURCES})

# 链接SMTParser
target_link_libraries(optismt_lib smtparser)

# 查找和链接优化求解器
# Gurobi
find_path(GUROBI_INCLUDE_DIR 
    NAMES gurobi_c++.h
    PATHS 
        $ENV{GUROBI_HOME}/include
        /opt/gurobi*/include
        /usr/local/include
        /usr/include
)

find_library(GUROBI_CXX_LIBRARY
    NAMES gurobi_c++
    PATHS
        $ENV{GUROBI_HOME}/lib
        /opt/gurobi*/lib
        /usr/local/lib
        /usr/lib
)

find_library(GUROBI_LIBRARY
    NAMES gurobi gurobi95 gurobi90 gurobi81
    PATHS
        $ENV{GUROBI_HOME}/lib
        /opt/gurobi*/lib
        /usr/local/lib
        /usr/lib
)

if(GUROBI_INCLUDE_DIR AND GUROBI_CXX_LIBRARY AND GUROBI_LIBRARY)
    message(STATUS "Found Gurobi: ${GUROBI_INCLUDE_DIR}")
    target_include_directories(optismt_lib PRIVATE ${GUROBI_INCLUDE_DIR})
    target_link_libraries(optismt_lib ${GUROBI_CXX_LIBRARY} ${GUROBI_LIBRARY})
    target_compile_definitions(optismt_lib PRIVATE HAVE_GUROBI)
else()
    message(WARNING "Gurobi not found. Gurobi backend will be disabled.")
endif()

# CPLEX (可选)
find_path(CPLEX_INCLUDE_DIR
    NAMES ilcplex/cplex.h
    PATHS
        $ENV{CPLEX_HOME}/include
        /opt/ibm/ILOG/CPLEX*/include
        /usr/local/include
        /usr/include
)

if(CPLEX_INCLUDE_DIR)
    message(STATUS "Found CPLEX: ${CPLEX_INCLUDE_DIR}")
    target_include_directories(optismt_lib PRIVATE ${CPLEX_INCLUDE_DIR})
    target_compile_definitions(optismt_lib PRIVATE HAVE_CPLEX)
else()
    message(WARNING "CPLEX not found. CPLEX backend will be disabled.")
endif()

# Z3 (可选)
find_package(PkgConfig QUIET)
if(PkgConfig_FOUND)
    pkg_check_modules(Z3 QUIET z3)
    if(Z3_FOUND)
        message(STATUS "Found Z3: ${Z3_VERSION}")
        target_include_directories(optismt_lib PRIVATE ${Z3_INCLUDE_DIRS})
        target_link_libraries(optismt_lib ${Z3_LIBRARIES})
        target_compile_definitions(optismt_lib PRIVATE HAVE_Z3)
    else()
        message(WARNING "Z3 not found. Z3 backend will be disabled.")
    endif()
endif()

# SCIP (可选)
find_path(SCIP_INCLUDE_DIR
    NAMES scip/scip.h
    PATHS
        /usr/local/include
        /usr/include
        /opt/scip/include
)

if(SCIP_INCLUDE_DIR)
    message(STATUS "Found SCIP: ${SCIP_INCLUDE_DIR}")
    target_include_directories(optismt_lib PRIVATE ${SCIP_INCLUDE_DIR})
    target_compile_definitions(optismt_lib PRIVATE HAVE_SCIP)
else()
    message(WARNING "SCIP not found. SCIP backend will be disabled.")
endif()

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

# 测试 (可选)
option(BUILD_TESTS "Build tests" OFF)
if(BUILD_TESTS)
    enable_testing()
    
    # 查找测试框架
    find_package(GTest QUIET)
    if(GTest_FOUND)
        add_subdirectory(tests)
    else()
        message(WARNING "Google Test not found. Tests will not be built.")
    endif()
endif()

# 文档生成 (可选)
option(BUILD_DOCS "Build documentation" OFF)
if(BUILD_DOCS)
    find_package(Doxygen QUIET)
    if(Doxygen_FOUND)
        set(DOXYGEN_IN ${CMAKE_CURRENT_SOURCE_DIR}/docs/Doxyfile.in)
        set(DOXYGEN_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)
        
        configure_file(${DOXYGEN_IN} ${DOXYGEN_OUT} @ONLY)
        
        add_custom_target(docs ALL
            COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYGEN_OUT}
            WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
            COMMENT "Generating API documentation with Doxygen"
            VERBATIM
        )
    else()
        message(WARNING "Doxygen not found. Documentation will not be generated.")
    endif()
endif()

# 包配置
set(CPACK_PACKAGE_NAME "OptiSMT")
set(CPACK_PACKAGE_VERSION "${PROJECT_VERSION}")
set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "SMT to Optimization Problem Transformer")
set(CPACK_PACKAGE_VENDOR "OptiSMT Team")
set(CPACK_PACKAGE_CONTACT "optismt@example.com")

include(CPack)

# 显示配置摘要
message(STATUS "")
message(STATUS "OptiSMT Configuration Summary:")
message(STATUS "  Version: ${PROJECT_VERSION}")
message(STATUS "  Build type: ${CMAKE_BUILD_TYPE}")
message(STATUS "  C++ standard: ${CMAKE_CXX_STANDARD}")
message(STATUS "  Install prefix: ${CMAKE_INSTALL_PREFIX}")
message(STATUS "")
message(STATUS "Optional dependencies:")
if(GUROBI_INCLUDE_DIR AND GUROBI_CXX_LIBRARY AND GUROBI_LIBRARY)
    message(STATUS "  Gurobi: Found")
else()
    message(STATUS "  Gurobi: Not found")
endif()
if(CPLEX_INCLUDE_DIR)
    message(STATUS "  CPLEX: Found")
else()
    message(STATUS "  CPLEX: Not found")
endif()
if(Z3_FOUND)
    message(STATUS "  Z3: Found")
else()
    message(STATUS "  Z3: Not found")
endif()
if(SCIP_INCLUDE_DIR)
    message(STATUS "  SCIP: Found")
else()
    message(STATUS "  SCIP: Not found")
endif()
message(STATUS "")
message(STATUS "Build options:")
message(STATUS "  Build tests: ${BUILD_TESTS}")
message(STATUS "  Build docs: ${BUILD_DOCS}")
message(STATUS "") 