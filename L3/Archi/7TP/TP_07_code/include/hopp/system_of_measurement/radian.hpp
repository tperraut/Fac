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


#ifndef HOPP_SYSTEM_OF_MEASUREMENT_RADIAN_HPP
#define HOPP_SYSTEM_OF_MEASUREMENT_RADIAN_HPP

#include <iostream>
#include <type_traits>

#include "../math/pi.hpp"
#include "degree.hpp"


namespace hopp
{
	// Forward declaration of class degree
	template <class T>
	class degree;
	
	/**
	 * @brief Radian (angle)
	 *
	 * @code
	 * #include <hopp/system_of_measurement.hpp>
	 * @endcode
	 *
	 * @b From http://en.wikipedia.org/wiki/Radian @n
	 * The radian is the standard unit of angular measure, used in many areas of mathematics. An angle's measurement in radians is numerically equal to the length of a corresponding arc of a unit circle, so one radian is just under 57.3 degrees (when the arc length is equal to the radius). The unit was formerly an SI supplementary unit, but this category was abolished in 1995 and the radian is now considered an SI derived unit. The SI unit of solid angle measurement is the steradian.
	 *
	 * @ingroup hopp_system_of_measurement
	 */
	template <class T>
	class radian
	{
	static_assert(std::is_arithmetic<T>::value, "hopp::radian works for arithmetic types only");
	
	private:
		
		/// Value of the angle in radian
		T m_value;
		
	public:
		
		/// @brief Construtor
		/// @param[in] radian_value Radian value (T(0) by default)
		explicit radian(T const & radian_value = T(0)) : m_value(radian_value) { }
		
		/// @brief Constructor with hopp::degree
		/// @param[in] degree A hopp::degree
		radian(hopp::degree<T> const & degree) : m_value(degree.radian_value()) { }
		
		/// @brief Operator= between hopp::radian and hopp::degree
		/// @param[in] degree A hopp::degree
		/// @return the hopp::radian
		hopp::radian<T> & operator =(hopp::degree<T> const & degree)
		{
			m_value = degree.radian_value();
			return *this;
		}
		
		/// @brief Return the radian value
		/// @return the radian value
		T const & value() const { return m_value; }
		
		/// @copydoc hopp::radian::value
		T const & radian_value() const { return value(); }
		
		/// @copydoc hopp::degree::value
		T degree_value() const { return ((value() * T(180)) / math::pi<T>()); }
		
		/// @brief Return a hopp::degree with converted value
		/// @return the a hopp::degree with converted value
		degree<T> to_degree() const { return hopp::degree<T>(degree_value()); }
	};
	
	/// @brief Operator << between a std::ostream and a hopp::radian<T>
	/// @param[in,out] out          A std::ostream
	/// @param[in]     angle_radian A hopp::radian<T>
	/// @return out
	/// @relates hopp::radian
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::radian<T> const & angle_radian)
	{
		out << angle_radian.value() << "rad";
		return out;
	}
	
	/// @brief Operator == between two hopp::radian<T>
	/// @param[in] a A hopp::radian<T>
	/// @param[in] b A hopp::radian<T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::radian
	template <class T>
	bool operator ==(hopp::radian<T> const & a, hopp::radian<T> const & b)
	{
		return a.value() == b.value();
	}
	
	/// @brief Operator != between two hopp::radian<T>
	/// @param[in] a A hopp::radian<T>
	/// @param[in] b A hopp::radian<T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::radian
	template <class T>
	bool operator !=(hopp::radian<T> const & a, hopp::radian<T> const & b)
	{
		return (a == b) == false;
	}
	
	/// @brief Operator < between two hopp::radian<T>
	/// @param[in] a A hopp::radian<T>
	/// @param[in] b A hopp::radian<T>
	/// @return true if a < b, false otherwise
	/// @relates hopp::radian
	template <class T>
	bool operator <(hopp::radian<T> const & a, hopp::radian<T> const & b)
	{
		return a.value() < b.value();
	}
	
	/// @brief Operator <= between two hopp::radian<T>
	/// @param[in] a A hopp::radian<T>
	/// @param[in] b A hopp::radian<T>
	/// @return true if a <= b, false otherwise
	/// @relates hopp::radian
	template <class T>
	bool operator <=(hopp::radian<T> const & a, hopp::radian<T> const & b)
	{
		return a < b || a == b;
	}
	
	/// @brief Operator > between two hopp::radian<T>
	/// @param[in] a A hopp::radian<T>
	/// @param[in] b A hopp::radian<T>
	/// @return true if a > b, false otherwise
	/// @relates hopp::radian
	template <class T>
	bool operator >(hopp::radian<T> const & a, hopp::radian<T> const & b)
	{
		return (a <= b) == false;
	}
	
	/// @brief Operator >= between two hopp::radian<T>
	/// @param[in] a A hopp::radian<T>
	/// @param[in] b A hopp::radian<T>
	/// @return true if a >= b, false otherwise
	/// @relates hopp::radian
	template <class T>
	bool operator >=(hopp::radian<T> const & a, hopp::radian<T> const & b)
	{
		return (a < b) == false;
	}
	
	/// @brief Make a hopp::radian<T>
	/// @param[in] radian_value Radian value
	/// @return hopp::radian<T>(radian_value)
	/// @relates hopp::radian
	template <class T>
	hopp::radian<T> make_radian(T const & radian_value)
	{
		return hopp::radian<T>(radian_value);
	}
}

#endif
