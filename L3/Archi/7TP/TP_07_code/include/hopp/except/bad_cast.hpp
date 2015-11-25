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


#ifndef HOPP_EXCEPT_BAD_CAST_HPP
#define HOPP_EXCEPT_BAD_CAST_HPP

#include <exception>
#include <stdexcept>


namespace hopp
{
	namespace except
	{
		/**
		 * @brief Exception "bad cast"
		 *
		 * @code
		   #include <hopp/except.hpp>
		   @endcode
		 *
		 * @ingroup hopp_except
		 */
		class bad_cast : public std::runtime_error
		{
		public:
			
			/// @brief Constructor
			/// @param[in] what_arg Description of the error
			explicit bad_cast(std::string const & what_arg) :
				std::runtime_error(what_arg)
			{ }
			
			/// @copydoc hopp::except::bad_cast::bad_cast(std::string const &)
			explicit bad_cast(char const * const what_arg) :
				std::runtime_error(what_arg)
			{ }
			
			/// @brief Return the description of the error
			/// @return the description of the error
			virtual char const * what() const noexcept
			{
				return std::runtime_error::what();
			}
		};
	}
}

#endif
