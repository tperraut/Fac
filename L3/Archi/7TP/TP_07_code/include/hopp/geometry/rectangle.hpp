// Copyright © 2014, 2015 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_GEOMETRY_RECTANGLE_HPP
#define HOPP_GEOMETRY_RECTANGLE_HPP

#include <iostream>


namespace hopp
{
	/**
	 * @brief Rectangle (left, top, width, size)
	 *
	 * @code
	   #include <hopp/geometry.hpp>
	   @endcode
	 *
	 * @ingroup hopp_geometry
	 */
	template <class T>
	class rectangle
	{
	public:
		
		/// Left coordinate
		T left;
		
		/// Top coordinate
		T top;
		
		/// Width
		T width;
		
		/// Height
		T height;
		
		/// @brief Default constructor
		rectangle() : left(), top(), width(), height() { }
		
		/// @brief Constructor
		/// @param[in] left   Left
		/// @param[in] top    Top
		/// @param[in] width  Width
		/// @param[in] height Height
		rectangle<T>(T const & left, T const & top, T const & width, T const & height) :
			left(left), top(top), width(width), height(height)
		{ }
		
		/// @brief Return right coordinate
		/// @return right
		T right() const { return left + width; }
		
		/// @brief Return bottom coordinate
		/// @return bottom
		T bottom() const { return top + height; }
	};
	
	/// @brief Operator << between a std::ostream and a hopp::rectangle<T>
	/// @param[in,out] out       A std::ostream
	/// @param[in]     rectangle A hopp::rectangle<T>
	/// @return out
	/// @relates hopp::rectangle
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::rectangle<T> const & rectangle)
	{
		out << "{ left = " << rectangle.left << ", top = " << rectangle.top << ", width = " << rectangle.width << ", height = " << rectangle.height << " }";
		return out;
	}
	
	/// @brief Operator == between two hopp::rectangle<T>
	/// @param[in] a A hopp::rectangle<T>
	/// @param[in] b A hopp::rectangle<T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::rectangle
	template <class T>
	bool operator ==(hopp::rectangle<T> const & a, hopp::rectangle<T> const & b)
	{
		return a.left == b.left && a.top == b.top && a.width == b.width && a.height == b.height;
	}
	
	/// @brief Operator != between two hopp::rectangle<T>
	/// @param[in] a A hopp::rectangle<T>
	/// @param[in] b A hopp::rectangle<T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::rectangle
	template <class T>
	bool operator !=(hopp::rectangle<T> const & a, hopp::rectangle<T> const & b)
	{
		return (a == b) == false;
	}
}

#endif
