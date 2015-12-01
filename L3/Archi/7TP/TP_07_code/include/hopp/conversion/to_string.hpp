// Copyright © 2012, 2013, 2015 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_CONVERSATION_TO_STRING_HPP
#define HOPP_CONVERSATION_TO_STRING_HPP

#include <sstream>
#include <string>
#include <iomanip>
#include <limits>


namespace hopp
{
	namespace
	{
		// To string with ostringstream (end)
		inline std::string ostringstream_to_string(std::ostringstream const & os)
		{
			return os.str();
		}
		
		// To string with ostringstream
		template <class T, class... args_t>
		std::string ostringstream_to_string(std::ostringstream & o, T const & t, args_t const & ... args)
		{
			o << t;
			return hopp::ostringstream_to_string(o, args...);
		}
	}
	
	/**
	 * @brief Get a std::string from an input
	 *
	 * @code
	   #include <hopp/conversion.hpp>
	   @endcode
	 *
	 * @param[in] args Inputs
	 *
	 * @return the std::string from the input
	 *
	 * @b Exemples
	 * @code
	   std::string s = hopp::to_string("A int = ", 5, ", and a char = ", 'a'); // A int = 5, and a char = a
	   @endcode
	 * @code
	   std::string s = hopp::to_string("A double (full precision) = ", std::setprecision(std::numeric_limits<double>::digits10 + 1), 3.14); // A double (full precision) = 3.14
	   @endcode
	 * @code
	   std::string s = hopp::to_string("A bool = ", true, ", with std::boolalpha = ", std::boolalpha, true); // A bool = 1, with std::boolalpha = true
	   @endcode
	 *
	 * @ingroup hopp_conversion
	 */
	template <class... args_t>
	std::string to_string(args_t const & ... args)
	{
		std::ostringstream o;
		return hopp::ostringstream_to_string(o, args...);
	}
}

#endif
