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


#ifndef HOPP_TEST_HPP
#define HOPP_TEST_HPP

/**
 * @defgroup hopp_test Test
 *
 * @brief Function for unit tests
 *
 * @code
   #include <hopp/test.hpp>
   @endcode
 */

#include <iostream>


namespace hopp
{
	/**
	 * @brief Returns 1 if test succeed, print the error and return 0 otherwise
	 * 
	 * If the expression is true:
	 * - return 1
	 *
	 * else (expression is false):
	 * - print the error message @n
	 * - return 0
	 *
	 * @b Example:
	 * @code
	   int main()
	   {
	   	int nb_test = 0;
	   	
	   	// Test
	   	++nb_test;
	   	nb_test -= hopp::test(1 == 1, "1 must be equal to 1\n");
	   	
	   	return nb_test;
	   }
	   @endcode
	 *
	 * @param[in]     expression Test
	 * @param[in]     what       Error message
	 * @param[in,out] out        A std::ostream (std::cout by default)
	 *
	 * @return 1 if test succeed, print the error and return 0 otherwise
	 *
	 * @ingroup hopp_test
	 */
	inline int test(bool const expression, std::string const & what, std::ostream & out = std::cout)
	{
		if (expression == false)
		{
			out << what; out.flush();
			return 0;
		}
		
		return 1;
	}
}

#endif
