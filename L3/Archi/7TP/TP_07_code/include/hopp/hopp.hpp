// Copyright © 2015 Lénaïc Bagnères, hnc@singularity.fr

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


/*! @mainpage hopp
 * 
 * https://gitlab.com/hnc/hopp @n
 * http://hnc.toile-libre.org/index.php?section=dev&page=hopp @n
 * https://www.lri.fr/~bagneres/index.php?section=dev&page=hopp
 *
 * @section section_hopp hopp
 *
 * Header-Only Program Parts
 * 
 * Basic (but useful), modern and generic C++14 header-only library
 * 
 * Apache License, Version 2.0 @n
 * GNU Affero General Public License 3+
 * 
 * @section section_system_requirement System Requirement
 * 
 * Required:
 * - C++11 compiler
 * 
 * Optional:
 * - CMake build system @n
 * - OpenMP @n
 * - OpenSSL
 * 
 * @section section_installation Installation
 * 
 * With CMake:
 * - @code
     mkdir build
     cd build
     cmake .. # -DCMAKE_INSTALL_PREFIX=/path/to/install # -DDEBUG=TRUE # -DDISABLE_TESTS=TRUE
     make
     # make doc
     # make test
     make install # su -c "make install" # sudo make install
     @endcode
 * 
 * Without CMake:
 * - This project is a header-only library, you can copy the include directory in /usr/local (for example) or in your project. (But you have to define some macros to enable optional parts.)
 * 
 * @section section_utilization Utilization
 * 
 * If you use CMake, add these lines in your CMakeLists.txt:
 * @code
   # hopp
   message(STATUS "---")
   find_package(hopp REQUIRED)
   # See /installation/path/lib/hopp/hopp-config.cmake for CMake variables
   @endcode
 */


#ifndef HOPP_HPP
#define HOPP_HPP

/**
 * @defgroup hopp_about About hopp
 * @copydoc hopp
 */

#include <string>


/**
 * @brief hopp (Header-Only Program Parts)
 * 
 * @code
   #include <hopp/hopp.hpp>
   @endcode
 */
namespace hopp
{
	/// @brief Version of hopp
	/// @return version of hopp
	/// @ingroup hopp_about
	inline std::string version() { return "0.0.0"; }
	
	/// @brief Codename of hopp
	/// @return codename of hopp
	/// @ingroup hopp_about
	inline std::string codename() { return "A New Beginning"; }
}

#endif
