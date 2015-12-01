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


#ifndef HOPP_CONTAINER_VECTOR3_HPP
#define HOPP_CONTAINER_VECTOR3_HPP

#include <iostream>


namespace hopp
{
	/**
	 * @brief Container for three T (x, y and z)
	 *
	 * @code
	   #include <hopp/container/vector3.hpp>
	   @endcode
	 *
	 * @ingroup hopp_container
	 */
	template <class T>
	class vector3
	{
	public:
		
		/// X
		T x;
		
		/// Y
		T y;
		
		/// Z
		T z;
		
		/// @brief Default constructor
		vector3() : x(), y(), z()
		{ }
		
		/// @brief Constructor
		/// @param[in] x X
		/// @param[in] y Y
		/// @param[in] z Z
		vector3(T const & x, T const & y, T const & z) : x(x), y(y), z(z)
		{ }
	};
	
	/// @brief Operator << between a std::ostream and a hopp::vector3<T>
	/// @param[in,out] out     A std::ostream
	/// @param[in]     vector3 A hopp::vector3<T>
	/// @return out
	/// @relates hopp::vector3
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::vector3<T> const & vector3)
	{
		out << "{ " << vector3.x << ", " << vector3.y << ", " << vector3.z << " }";
		return out;
	}
	
	/// @brief Operator == between two hopp::vector3<T>
	/// @param[in] a A hopp::vector3<T>
	/// @param[in] b A hopp::vector3<T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::vector3
	template <class T>
	bool operator ==(hopp::vector3<T> const & a, hopp::vector3<T> const & b)
	{
		return a.x == b.x && a.y == b.y && a.z == b.z;
	}
	
	/// @brief Operator != between two hopp::vector3<T>
	/// @param[in] a A hopp::vector3<T>
	/// @param[in] b A hopp::vector3<T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::vector3
	template <class T>
	bool operator !=(hopp::vector3<T> const & a, hopp::vector3<T> const & b)
	{
		return (a == b) == false;
	}
	
	/// @brief Operator < between two hopp::vector3<T>
	/// @param[in] a A hopp::vector3<T>
	/// @param[in] b A hopp::vector3<T>
	/// @return true if a < b, false otherwise
	/// @relates hopp::vector3
	template <class T>
	bool operator <(hopp::vector3<T> const & a, hopp::vector3<T> const & b)
	{
		if (a.x < b.x) { return true; }
		if (a.y < b.y) { return true; }
		else { return a.z < b.z; }
	}
	
	/// @brief Operator <= between two hopp::vector3<T>
	/// @param[in] a A hopp::vector3<T>
	/// @param[in] b A hopp::vector3<T>
	/// @return true if a <= b, false otherwise
	/// @relates hopp::vector3
	template <class T>
	bool operator <=(hopp::vector3<T> const & a, hopp::vector3<T> const & b)
	{
		return a < b || a == b;
	}
	
	/// @brief Operator > between two hopp::vector3<T>
	/// @param[in] a A hopp::vector3<T>
	/// @param[in] b A hopp::vector3<T>
	/// @return true if a > b, false otherwise
	/// @relates hopp::vector3
	template <class T>
	bool operator >(hopp::vector3<T> const & a, hopp::vector3<T> const & b)
	{
		return (a <= b) == false;
	}
	
	/// @brief Operator >= between two hopp::vector3<T>
	/// @param[in] a A hopp::vector3<T>
	/// @param[in] b A hopp::vector3<T>
	/// @return true if a >= b, false otherwise
	/// @relates hopp::vector3
	template <class T>
	bool operator >=(hopp::vector3<T> const & a, hopp::vector3<T> const & b)
	{
		return (a < b) == false;
	}
}

#endif
