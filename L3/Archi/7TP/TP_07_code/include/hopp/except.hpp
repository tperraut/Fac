// Copyright © 2013, 2014, 2015 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_EXCEPT_HPP
#define HOPP_EXCEPT_HPP

/**
 * @defgroup hopp_except Exception
 * @copydoc hopp::except
 */

#include <exception>
#include <stdexcept>


namespace hopp
{
	/**
	 * @brief Extends std::exception, std::logic_error and std::runtime_error
	 *
	 * @code
	   #include <hopp/except.hpp>
	   @endcode
	 *
	 * std::exception @n
	 * http://www.cplusplus.com/reference/exception/exception/ @n
	 * http://en.cppreference.com/w/cpp/error/exception
	 *
	 * std::logic_error @n
	 * http://www.cplusplus.com/reference/stdexcept/logic_error/ @n
	 * http://en.cppreference.com/w/cpp/error/logic_error
	 *
	 * std::runtime_error @n
	 * http://www.cplusplus.com/reference/stdexcept/runtime_error/ @n
	 * http://en.cppreference.com/w/cpp/error/runtime_error
	 */
	namespace except
	{
		// Just for Doxygen
	}
}

#include "except/bad_cast.hpp"
#include "except/conversion_error.hpp"
#include "except/file_not_found.hpp"
#include "except/incomplete_implementation.hpp"
#include "except/parse_error.hpp"

#endif
