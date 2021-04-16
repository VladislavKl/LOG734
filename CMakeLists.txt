cmake_minimum_required(VERSION 3.16)
project(MKP_Heuristics)

set(CMAKE_CXX_STANDARD 17)

#add_definitions(-DDEBUG_INFO)

SET(CMAKE_CXX_FLAGS_RELEASE "-O3 -Wall -Wextra")
#SET(CMAKE_CXX_FLAGS_DEBUG "-g -Wall -Wextra")

add_executable(Assignment_1 Assignment\ 1/main.cpp)
add_executable(Assignment_2 Assignment\ 2/main.cpp)
add_executable(Assignment_3 Assignment\ 3/main.cpp)