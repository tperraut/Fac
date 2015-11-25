# Copyright © 2015 Lénaïc Bagnères, hnc@singularity.fr

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


cmake_minimum_required(VERSION 2.6)


# General C++ flags
	
	# General
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wconversion -Wsign-conversion -std=c++11 -pedantic -fopenmp")
	
	# Release / Debug flags
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -DNDEBUG -march=native -ffast-math")
	#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -DNDEBUG")
	#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -g3")


# Local
	message(STATUS "---")
	set(local_INCLUDE "./include")
	include_directories("${local_INCLUDE}")
	message(STATUS "Include local = ${local_INCLUDE}")


# Compiler log
	message(STATUS "---")
	message(STATUS "C++ compiler = ${CMAKE_CXX_COMPILER}")
	message(STATUS "C++ flags    = ${CMAKE_CXX_FLAGS}")


# Tests
	
	message(STATUS "---")
	
	# Tests
	if (DISABLE_TESTS)
		
		message(STATUS "Tests are disabled")
		
	else()
		
		enable_testing()
		
		file(GLOB_RECURSE tests tests/*.cpp)
		
		foreach(test_source ${tests})
		
			# Get test name and source
			string(REPLACE ".cpp" "" test_name ${test_source})
			string(REPLACE "${CMAKE_CURRENT_SOURCE_DIR}/tests/" "test__" test_name ${test_name})
			string(REPLACE "/" "_" test_name ${test_name})
			
			message(STATUS "Add test ${test_name}")
			
			add_executable(${test_name} "${test_source}")
			
			add_test(${test_name} "${test_name}")
			
		endforeach()
		
	endif()


# Doxygen
	# TODO See https://gitlab.com/hnc/hopp/blob/master/CMakeLists.txt
	#message(STATUS "---")
	#file(MAKE_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/build/doxygen")
	#set(DOXYGEN_WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include")
	#find_package(hopp_doxygen PATHS "${HOPP_CMAKE_PATH}" NO_DEFAULT_PATH)


# Install
	# .hpp
	install(DIRECTORY include/ DESTINATION include FILES_MATCHING PATTERN "*.hpp")
	# .cmake
	# TODO See https://gitlab.com/hnc/hopp/blob/master/CMakeLists.txt
	#install(FILES cmake/hopp-config.cmake DESTINATION lib/hopp)
	# Doxygen
	# TODO See https://gitlab.com/hnc/hopp/blob/master/CMakeLists.txt
	#install(DIRECTORY build/doxygen DESTINATION share/hopp)


# Little help
	message(STATUS "---")
	message(STATUS "You can execute:")
	message(STATUS "    make         # To compile executables and tests")
	message(STATUS "    make test    # To execute tests")
	message(STATUS "    make install # To install library, include and CMake module")
	message(STATUS "                 # If you need root access:")
	message(STATUS "                 #     sudo make install")
	message(STATUS "                 #     su -c \"make install\"")
	if (DOXYGEN_FOUND AND DOXYGEN_WORKING_DIRECTORY AND HOPP_DOXYFILE)
		message(STATUS "    make doxygen # To generate the API documentation with Doxygen")
	endif()
