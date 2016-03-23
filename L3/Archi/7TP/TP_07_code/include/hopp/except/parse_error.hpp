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


#ifndef HOPP_EXCEPT_PARSE_ERROR_HPP
#define HOPP_EXCEPT_PARSE_ERROR_HPP

#include <exception>
#include <stdexcept>


namespace hopp
{
	namespace except
	{
		/**
		 * @brief Exception "parse error"
		 *
		 * @code
		   #include <hopp/except.hpp>
		   @endcode
		 *
		 * @ingroup hopp_except
		 */
		class parse_error : public std::runtime_error
		{
		protected:
			
			/// @brief Line number
			unsigned int m_line_number;
			
			/// @brief Column number
			unsigned int m_column_number;
			
		public:

			/// @brief Constructor
			/// @param[in] what_arg      Description of the error
			/// @param[in] line_number   Line number
			/// @param[in] column_number Column number
			explicit parse_error(std::string const & what_arg, unsigned int line_number = 0, unsigned int column_number = 0) :
				std::runtime_error(what_arg),
				m_line_number(line_number),
				m_column_number(column_number)
			{ }
			
			/// @brief Constructor
			/// @param[in] what_arg      Description of the error
			/// @param[in] line_number   Line number
			/// @param[in] column_number Column number
			explicit parse_error(char const * const what_arg, unsigned int line_number = 0, unsigned int column_number = 0) :
				std::runtime_error(what_arg),
				m_line_number(line_number),
				m_column_number(column_number)
			{ }
			
			/// @brief Return the description of the error
			/// @return the description of the error
			virtual char const * what() const noexcept
			{
				return std::runtime_error::what();
			}
			
			/// @brief Return the line number of the error
			/// @return the line number of the error
			virtual unsigned int line_number() const { return m_line_number; }
			
			/// @brief Return the column number of the error
			/// @return the column number of the error
			virtual unsigned int column_number() const { return m_column_number; }
		};
	}
}

#endif
