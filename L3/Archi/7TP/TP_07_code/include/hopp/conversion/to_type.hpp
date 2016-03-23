// Copyright © 2012, 2014, 2015 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_CONVERSATION_TO_TYPE_HPP
#define HOPP_CONVERSATION_TO_TYPE_HPP

#include <sstream>
#include <type_traits>

#include "../except/conversion_error.hpp"
#include "to_string.hpp"


namespace hopp
{
	namespace
	{
		// Convert a T into a return_t
		template <class return_t, class T>
		class conversion_to_
		{
		public:
			
			static return_t call(T const & in)
			{
				std::stringstream ss;
				set_precision(ss, std::is_floating_point<T>());
				ss << in;
				
				return_t r;
				ss >> r;
				
				#ifndef NDEBUG
					if (bool(ss) == false) { throw hopp::except::conversion_error("hopp::conversion: error: invalid conversion"); }
				#endif
				
				return r;
			}
			
		private:
			
			// T
			static void set_precision(std::stringstream & /*ss*/, std::false_type /*tag*/)
			{ }
			
			// Floating point
			static void set_precision(std::stringstream & ss, std::true_type /*tag*/)
			{
				ss.precision(std::numeric_limits<T>::digits10 + 2);
			}
		};
		
		// Partial specialization when return_t is std::string as
		template <class T>
		class conversion_to_<std::string, T>
		{
		public:
			static std::string call(T const & in) { return hopp::to_string(in); }
		};
	}
	
	/**
	 * @brief Convert an input into a another type
	 *
	 * @code
	   #include <hopp/conversion.hpp>
	   @endcode
	 * 
	 * The input is converted into the return_t type (using a std::stringstream to do the conversion)
	 *
	 * @param[in] in Input
	 *
	 * Partial specialization when:
	 * - return_t is std::string (call hopp::to_string)
	 *
	 * @return the return_t from the input
	 *
	 * @b Exemple:
	 * @code
	   // return_type output = hopp::to_<return_type>(input);
	      int         output = hopp::to_<int>        ("420");
	   @endcode
	 *
	 * @note Prefer the hopp::to_type(e) function!
	 * @code
	   int i = hopp::to_<int>("42"); // You can use hopp::to_int
	   double d = hopp::to_<double>("42.1"); // You can use hopp::to_double
	   @endcode
	 *
	 * @note Consider Boost.Coerce or Boost.Lexical_Cast for safe conversions
	 *
	 * @ingroup hopp_conversion
	 */
	template <class return_t, class T>
	return_t to_(T const & in)
	{
		return hopp::conversion_to_<return_t, T>::call(in);
	}
}

#endif
