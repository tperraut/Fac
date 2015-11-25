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


#ifndef HOPP_CONTAINER_OPTIONAL_HPP
#define HOPP_CONTAINER_OPTIONAL_HPP

#include <iostream>
#include <stdexcept>


namespace hopp
{
	/**
	 * @brief Container for an optional value
	 *
	 * @code
	   #include <hopp/container/optional.hpp>
	   @endcode
	 *
	 * @ingroup hopp_container
	 */
	template <class T>
	class optional
	{
	private:
		
		/// Value is engaged?
		bool m_engaged;
		
		/// Value
		T m_value;
		
	public:
		
		/// @brief Default constructor
		optional() : m_engaged(false)
		{ }
		
		/// @brief Constructor
		/// @param[in] value Value
		optional(T const & value) : m_engaged(true), m_value(value)
		{ }
		
		/// @brief Optional is engaged?
		/// @return true if engaged, false otherwise
		bool is_engaged() const { return m_engaged; }
		
		/// @brief Optional is engaged?
		/// @return true if engaged, false otherwise
		operator bool() const { return is_engaged(); }
		
		/// @brief Get value
		/// @pre Value is engaged
		/// @return value
		T const & value() const
		{
			#ifndef NDEBUG
				if (m_engaged == false) { throw std::logic_error("hopp::optional::value: value is disengaged"); }
			#endif
			
			return m_value;
		}
		
		/// @brief Get value
		/// @pre Value is engaged
		/// @return value
		T & value()
		{
			#ifndef NDEBUG
				if (m_engaged == false) { throw std::logic_error("hopp::optional::value: value is disengaged"); }
			#endif
			
			return m_value;
		}
		
		/// @brief Get value
		/// @pre Value is engaged
		/// @return value
		T const & operator *() const { return value(); }
		
		/// @brief Get value
		/// @pre Value is engaged
		/// @return value
		T & operator *() { return value(); }
		
		/// @brief Get a pointer on the value
		/// @pre Value is engaged
		/// @return a pointer on the value
		T const * operator ->() const { return &value(); }
		
		/// @brief Get a pointer on the value
		/// @pre Value is engaged
		/// @return a pointer on the value
		T * operator ->() { return &value(); }
	};
	
	/// @brief Operator << between a std::ostream and a hopp::optional<T>
	/// @param[in,out] out      A std::ostream
	/// @param[in]     optional A hopp::optional<T>
	/// @return out
	/// @relates hopp::optional
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::optional<T> const & optional)
	{
		if (optional) { out << optional.value(); }
		else { out << "(disengaged)"; }
		return out;
	}
}

#endif
