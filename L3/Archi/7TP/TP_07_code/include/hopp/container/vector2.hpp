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


#ifndef HOPP_CONTAINER_VECTOR2_HPP
#define HOPP_CONTAINER_VECTOR2_HPP

#include <iostream>


namespace hopp
{
	/**
	 * @brief Container for two T (x and y)
	 *
	 * @code
	   #include <hopp/container/vector2.hpp>
	   @endcode
	 *
	 * @ingroup hopp_container
	 */
	template <class T>
	class vector2
	{
	public:
		
		/// X
		T x;
		
		/// Y
		T y;
		
		/// @brief Default constructor
		vector2() : x(), y()
		{ }
		
		/// @brief Constructor
		/// @param[in] x X
		/// @param[in] y Y
		vector2(T const & x, T const & y) : x(x), y(y)
		{ }
	};
	
	/// @brief Operator << between a std::ostream and a hopp::vector2<T>
	/// @param[in,out] out     A std::ostream
	/// @param[in]     vector2 A hopp::vector2<T>
	/// @return out
	/// @relates hopp::vector2
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::vector2<T> const & vector2)
	{
		out << "{ " << vector2.x << ", " << vector2.y << " }";
		return out;
	}
	
	/// @brief Operator == between two hopp::vector2<T>
	/// @param[in] a A hopp::vector2<T>
	/// @param[in] b A hopp::vector2<T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::vector2
	template <class T>
	bool operator ==(hopp::vector2<T> const & a, hopp::vector2<T> const & b)
	{
		return a.x == b.x && a.y == b.y;
	}
	
	/// @brief Operator != between two hopp::vector2<T>
	/// @param[in] a A hopp::vector2<T>
	/// @param[in] b A hopp::vector2<T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::vector2
	template <class T>
	bool operator !=(hopp::vector2<T> const & a, hopp::vector2<T> const & b)
	{
		return (a == b) == false;
	}
	
	/// @brief Operator < between two hopp::vector2<T>
	/// @param[in] a A hopp::vector2<T>
	/// @param[in] b A hopp::vector2<T>
	/// @return true if a < b, false otherwise
	/// @relates hopp::vector2
	template <class T>
	bool operator <(hopp::vector2<T> const & a, hopp::vector2<T> const & b)
	{
		if (a.x < b.x) { return true; }
		else { return a.y < b.y; }
	}
	
	/// @brief Operator <= between two hopp::vector2<T>
	/// @param[in] a A hopp::vector2<T>
	/// @param[in] b A hopp::vector2<T>
	/// @return true if a <= b, false otherwise
	/// @relates hopp::vector2
	template <class T>
	bool operator <=(hopp::vector2<T> const & a, hopp::vector2<T> const & b)
	{
		return a < b || a == b;
	}
	
	/// @brief Operator > between two hopp::vector2<T>
	/// @param[in] a A hopp::vector2<T>
	/// @param[in] b A hopp::vector2<T>
	/// @return true if a > b, false otherwise
	/// @relates hopp::vector2
	template <class T>
	bool operator >(hopp::vector2<T> const & a, hopp::vector2<T> const & b)
	{
		return (a <= b) == false;
	}
	
	/// @brief Operator >= between two hopp::vector2<T>
	/// @param[in] a A hopp::vector2<T>
	/// @param[in] b A hopp::vector2<T>
	/// @return true if a >= b, false otherwise
	/// @relates hopp::vector2
	template <class T>
	bool operator >=(hopp::vector2<T> const & a, hopp::vector2<T> const & b)
	{
		return (a < b) == false;
	}
}

#endif
