// Copyright © 2013, 2014 Inria, Written by Lénaïc Bagnères, lenaic.bagneres@inria.fr
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


#ifndef HOPP_SYSTEM_OF_MEASUREMENT_DEGREE_HPP
#define HOPP_SYSTEM_OF_MEASUREMENT_DEGREE_HPP

#include <iostream>
#include <type_traits>

#include "../math/pi.hpp"
#include "radian.hpp"


namespace hopp
{
	// Forward declaration of class radian
	template <class T>
	class radian;
	
	/**
	 * @brief Degree (angle)
	 *
	 * @code
	   #include <hopp/system_of_measurement.hpp>
	   @endcode
	 *
	 * @b From http://en.wikipedia.org/wiki/Degree_%28angle%29 @n
	 * A degree (in full, a degree of arc, arc degree, or arcdegree), usually denoted by ° (the degree symbol), is a measurement of plane angle, representing @f$ \frac{1}{360} @f$ of a full rotation; one degree is equivalent to @f$ \frac{\Pi}{180} @f$ radians. It is not an SI unit, as the SI unit for angles is radian, but it is mentioned in the SI brochure as an accepted unit.
	 *
	 * @ingroup hopp_system_of_measurement
	 */
	template <class T>
	class degree
	{
	static_assert(std::is_arithmetic<T>::value, "hopp::degree works for arithmetic types only");
	
	private:
		
		/// Value of the angle in degree
		T m_value;
		
	public:
		
		/// @brief Construtor
		/// @param[in] degree_value Degree value (T(0) by default)
		explicit degree(T const & degree_value = T(0)) : m_value(degree_value) { }
		
		/// @brief Constructor with hopp::radian
		/// @param[in] radian A hopp::radian
		degree(hopp::radian<T> const & radian) : m_value(radian.degree_value()) { }
		
		/// @brief Operator= between hopp::degree and hopp::radian
		/// @param[in] radian A hopp::radian
		/// @return the hopp::degree
		hopp::degree<T> & operator =(hopp::radian<T> const & radian)
		{
			m_value = radian.degree_value();
			return *this;
		}
		
		/// @brief Return the degree value
		/// @return the degree value
		T const & value() const { return m_value; }
		
		/// @copydoc hopp::degree::value
		T const & degree_value() const { return value(); }
		
		/// @copydoc hopp::radian::value
		T radian_value() const { return ((value() * math::pi<T>()) / T(180)); }
		
		/// @brief Return a hopp::radian with converted value
		/// @return the a hopp::radian with converted value
		radian<T> to_radian() const { return hopp::radian<T>(radian_value()); }
	};
	
	/// @brief Operator << between a std::ostream and a hopp::degree<T>
	/// @param[in,out] out          A std::ostream
	/// @param[in]     angle_degree A hopp::degree<T>
	/// @return out
	/// @relates hopp::degree
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::degree<T> const & angle_degree)
	{
		out << angle_degree.value() << "°";
		return out;
	}
	
	/// @brief Operator == between two hopp::degree<T>
	/// @param[in] a A hopp::degree<T>
	/// @param[in] b A hopp::degree<T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::degree
	template <class T>
	bool operator ==(hopp::degree<T> const & a, hopp::degree<T> const & b)
	{
		return a.value() == b.value();
	}
	
	/// @brief Operator != between two hopp::degree<T>
	/// @param[in] a A hopp::degree<T>
	/// @param[in] b A hopp::degree<T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::degree
	template <class T>
	bool operator !=(hopp::degree<T> const & a, hopp::degree<T> const & b)
	{
		return (a == b) == false;
	}
	
	/// @brief Operator < between two hopp::degree<T>
	/// @param[in] a A hopp::degree<T>
	/// @param[in] b A hopp::degree<T>
	/// @return true if a < b, false otherwise
	/// @relates hopp::degree
	template <class T>
	bool operator <(hopp::degree<T> const & a, hopp::degree<T> const & b)
	{
		return a.value() < b.value();
	}
	
	/// @brief Operator <= between two hopp::degree<T>
	/// @param[in] a A hopp::degree<T>
	/// @param[in] b A hopp::degree<T>
	/// @return true if a <= b, false otherwise
	/// @relates hopp::degree
	template <class T>
	bool operator <=(hopp::degree<T> const & a, hopp::degree<T> const & b)
	{
		return a < b || a == b;
	}
	
	/// @brief Operator > between two hopp::degree<T>
	/// @param[in] a A hopp::degree<T>
	/// @param[in] b A hopp::degree<T>
	/// @return true if a > b, false otherwise
	/// @relates hopp::degree
	template <class T>
	bool operator >(hopp::degree<T> const & a, hopp::degree<T> const & b)
	{
		return (a <= b) == false;
	}
	
	/// @brief Operator >= between two hopp::degree<T>
	/// @param[in] a A hopp::degree<T>
	/// @param[in] b A hopp::degree<T>
	/// @return true if a >= b, false otherwise
	/// @relates hopp::degree
	template <class T>
	bool operator >=(hopp::degree<T> const & a, hopp::degree<T> const & b)
	{
		return (a < b) == false;
	}
	
	/// @brief Make a hopp::degree<T>
	/// @param[in] degree_value Degree value
	/// @return hopp::degree<T>(degree_value)
	/// @relates hopp::degree
	template <class T>
	hopp::degree<T> make_degree(T const & degree_value)
	{
		return hopp::degree<T>(degree_value);
	}
}

#endif
