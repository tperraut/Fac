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


#ifndef HOPP_COLOR_HPP
#define HOPP_COLOR_HPP

/**
 * @defgroup hopp_color Color
 * @copydoc hopp::color
 */

#include <iostream>
#include <cstdint>

#include "int/uint8.hpp"
#include "algo/to_upper.hpp"
#include "conversion/to_string.hpp"


namespace hopp
{
	/**
	 * @brief Color (rgba: red green blue alpha)
	 * 
	 * r, g, b and a are between 0 and 255
	 * 
	 * @code
	   #include <hopp/color.hpp>
	   @endcode
	 *
	 * @ingroup hopp_color
	 */
	class color
	{
	public:
		
		/// Red level
		hopp::uint8 r;
		
		/// Green level
		hopp::uint8 g;
		
		/// Blue level
		hopp::uint8 b;
		
		/// Alpha level (transparency)
		hopp::uint8 a;
		
		/// @brief Default constructor
		color() :
			r(0u),
			g(0u),
			b(0u),
			a(255u)
		{ }
		
		/// @brief Constructor
		/// @param[in] r Red level
		/// @param[in] g Green level
		/// @param[in] b Blue level
		/// @param[in] a Alpha level (transparency) (255u by default)
		color
		(
			hopp::uint8 const & r,
			hopp::uint8 const & g,
			hopp::uint8 const & b,
			hopp::uint8 const & a = 255u
		) :
			r(r), g(g), b(b), a(a)
		{ }
		
		/// @brief HTML code of the color
		/// @return HTML code of the color
		std::string html()
		{
			return hopp::algo::to_upper_copy
			(
				std::string("#") +
				hopp::to_string(std::setw(2), std::setfill('0'), std::hex, r) +
				hopp::to_string(std::setw(2), std::setfill('0'), std::hex, g) +
				hopp::to_string(std::setw(2), std::setfill('0'), std::hex, b)
			);
		}
		
		// Basic colors
		
		/// @brief Black color
		/// @return Black color
		static hopp::color black() { return { 0u, 0u, 0u }; }
		
		/// @brief White color
		/// @return White color
		static hopp::color white() { return { 255u, 255u, 255u }; }
		
		/// @brief Grey color
		/// @return Grey color
		static hopp::color grey() { return { 128u, 128u, 128u }; }
		
		// LaTeX colors
		
		#include "color/private/latex.hpp"
	};
	
	/// @brief Operator == between two hopp::color
	/// @param[in] a A hopp::color
	/// @param[in] b A hopp::color
	/// @return true if the hopp::color are equal, false otherwise
	/// @relates hopp::color
	inline bool operator ==(hopp::color const & a, hopp::color const & b)
	{
		return a.r == b.r && a.g == b.g && a.b == b.b && a.a == b.a;
	}
	
	/// @brief Operator != between two hopp::color
	/// @param[in] a A hopp::color
	/// @param[in] b A hopp::color
	/// @return true if the hopp::color are different, false otherwise
	/// @relates hopp::color
	inline bool operator !=(hopp::color const & a, hopp::color const & b)
	{
		return !(a == b);
	}
	
	/// @brief Operator < between two hopp::color
	/// @param[in] a A hopp::color
	/// @param[in] b A hopp::color
	/// @return true if a < b, false otherwise
	/// @relates hopp::color
	inline bool operator <(hopp::color const & a, hopp::color const & b)
	{
		if (a.r != b.r) { return a.r < b.r; }
		if (a.g != b.g) { return a.g < b.g; }
		if (a.b != b.b) { return a.b < b.b; }
		if (a.a != b.a) { return a.a < b.a; }
		return false;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::color
	/// @param[in,out] o     Output stream
	/// @param[in]     color A hopp::color
	/// @return the output stream
	/// @relates hopp::color
	inline std::ostream & operator <<(std::ostream & o, hopp::color const & color)
	{
		o << "{ " << color.r << ", " << color.g << ", " << color.b << ", " << color.a << " }";
		return o;
	}
}

namespace std
{
	/// @brief Specialization of std::less for hopp::color
	/// @relates hopp::color
	template <>
	struct less<hopp::color>
	{
		/// @brief std::less between two hopp::color
		/// @param[in] a A hopp::color
		/// @param[in] b A hopp::color
		/// @return true if a < b, false otherwise
		bool operator()(hopp::color const & a, hopp::color const & b) const
		{
			if (a.r != b.r) { return a.r < b.r; }
			if (a.g != b.g) { return a.g < b.g; }
			if (a.b != b.b) { return a.b < b.b; }
			if (a.a != b.a) { return a.a < b.a; }
			return false;
		}
	};
	
	/// @brief Specialization of std::hash for hopp::color
	/// @relates hopp::color
	template <>
	struct hash<hopp::color>
	{
		size_t operator()(hopp::color const & color) const
		{
			uint_fast32_t tmp = 0;
			tmp += color.r; tmp = tmp << 8;
			tmp += color.g; tmp = tmp << 8;
			tmp += color.b; tmp = tmp << 8;
			tmp += color.a; tmp = tmp << 8;
			return std::hash<uint_fast32_t>()(tmp);
		}
	};
}

#endif
