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


#ifndef HOPP_INT_INT8_HPP
#define HOPP_INT_INT8_HPP

#include <iostream>
#include <limits>


namespace hopp
{
	/**
	 * @brief int with values between -128 and 127
	 *
	 * @code
	   #include <hopp/int.hpp>
	   @endcode
	 *
	 * @ingroup hopp_int_and_float
	 */
	class int8
	{
	public:
		
		/// int
		#if (CHAR_BIT == 8)
			signed char i;
		#else
			signed char i:8;
		#endif
		
	public:
		
		/// @brief Constructor from signed char
		/// @param[in] i Integer between -128 and 127
		int8(signed char const i = 0) : i(i) { }
		
		/// @brief Constructor from int
		/// @param[in] i Integer between -128 and 127
		int8(int const i) : i(static_cast<signed char>(i)) { }
		
		/// @brief Conversion operator to int
		/// @return a int from the hopp::int8
		operator int() const { return int(i); }
	};
	
	// +
	
	/// @brief Operator + between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return a + b
	/// @relates hopp::int8
	inline hopp::int8 operator +(hopp::int8 const a, hopp::int8 const b)
	{
		return int(a.i) + int(b.i);
	}
	/// @brief Operator + between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return a + b
	/// @relates hopp::int8
	inline int operator +(hopp::int8 const a, int const b)
	{
		return int(a.i) + b;
	}
	/// @brief Operator + between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return a + b
	/// @relates hopp::int8
	inline int operator +(int const a, hopp::int8 const b)
	{
		return a + int(b.i);
	}
	
	/// @brief Operator += between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return a += b
	/// @relates hopp::int8
	inline hopp::int8 & operator +=(hopp::int8 & a, hopp::int8 const b)
	{
		a = a + b;
		return a;
	}
	/// @brief Operator += between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return a += b
	/// @relates hopp::int8
	inline hopp::int8 operator +=(hopp::int8 & a, int const b)
	{
		a = a + b;
		return a;
	}
	/// @brief Operator += between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return a += b
	/// @relates hopp::int8
	inline int & operator +=(int & a, hopp::int8 const b)
	{
		a = a + b;
		return a;
	}
	
	/// @brief Operator ++ (prefix) with a hopp::int8
	/// @param[in] i A hopp::int8
	/// @return i++
	/// @relates hopp::int8
	inline hopp::int8 & operator ++(hopp::int8 & i)
	{
		++i.i;
		return i;
	}
	
	/// @brief Operator ++ (postfix) with a hopp::int8
	/// @param[in] i A hopp::int8
	/// @return i++
	/// @relates hopp::int8
	inline hopp::int8 operator ++(hopp::int8 & i, int)
	{
		hopp::int8 tmp = i;
		++i;
		return tmp;
	}
	
	// -
	
	/// @brief Operator - between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return a - b
	/// @relates hopp::int8
	inline hopp::int8 operator -(hopp::int8 const a, hopp::int8 const b)
	{
		return int(a.i) - int(b.i);
	}
	/// @brief Operator - between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return a - b
	/// @relates hopp::int8
	inline int operator -(hopp::int8 const a, int const b)
	{
		return int(a.i) - b;
	}
	/// @brief Operator - between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return a - b
	/// @relates hopp::int8
	inline int operator -(int const a, hopp::int8 const b)
	{
		return a - int(b.i);
	}
	
	/// @brief Operator -= between the hopp::int8two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return a -= b
	/// @relates hopp::int8
	inline hopp::int8 & operator -=(hopp::int8 & a, hopp::int8 const b)
	{
		a = a - b;
		return a;
	}
	/// @brief Operator -= between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return a -= b
	/// @relates hopp::int8
	inline hopp::int8 & operator -=(hopp::int8 & a, int const b)
	{
		a = a - b;
		return a;
	}
	/// @brief Operator -= between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return a -= b
	/// @relates hopp::int8
	inline int & operator -=(int & a, hopp::int8 const b)
	{
		a = a - b;
		return a;
	}
	
	/// @brief Operator -- (prefix) with a hopp::int8
	/// @param[in] i A hopp::int8
	/// @return i--
	/// @relates hopp::int8
	inline hopp::int8 & operator --(hopp::int8 & i)
	{
		--i.i;
		return i;
	}
	
	/// @brief Operator -- (postfix) with a hopp::int8
	/// @param[in] i A hopp::int8
	/// @return i--
	/// @relates hopp::int8
	inline hopp::int8 operator --(hopp::int8 & i, int)
	{
		hopp::int8 tmp = i;
		--i;
		return tmp;
	}
	
	// *
	
	/// @brief Operator * between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return a * b
	/// @relates hopp::int8
	inline hopp::int8 operator *(hopp::int8 const a, hopp::int8 const b)
	{
		return int(a.i) * int(b.i);
	}
	/// @brief Operator * between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return a * b
	/// @relates hopp::int8
	inline int operator *(hopp::int8 const a, int const b)
	{
		return int(a.i) * b;
	}
	/// @brief Operator * between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return a * b
	/// @relates hopp::int8
	inline int operator *(int const a, hopp::int8 const b)
	{
		return a * int(b.i);
	}
	
	/// @brief Operator *= between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return a *= b
	/// @relates hopp::int8
	inline hopp::int8 & operator *=(hopp::int8 & a, hopp::int8 const b)
	{
		a = a * b;
		return a;
	}
	/// @brief Operator *= between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return a *= b
	/// @relates hopp::int8
	inline hopp::int8 & operator *=(hopp::int8 & a, int const b)
	{
		a = a * b;
		return a;
	}
	/// @brief Operator *= between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return a *= b
	/// @relates hopp::int8
	inline int & operator *=(int & a, hopp::int8 const b)
	{
		a = a * b;
		return a;
	}
	
	// /
	
	/// @brief Operator / between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return a / b
	/// @relates hopp::int8
	inline hopp::int8 operator /(hopp::int8 const a, hopp::int8 const b)
	{
		return int(a.i) / int(b.i);
	}
	/// @brief Operator / between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return a / b
	/// @relates hopp::int8
	inline int operator /(hopp::int8 const a, int const b)
	{
		return int(a.i) / b;
	}
	/// @brief Operator / between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return a / b
	/// @relates hopp::int8
	inline int operator /(int const a, hopp::int8 const b)
	{
		return a / int(b.i);
	}
	
	/// @brief Operator /= between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return a /= b
	/// @relates hopp::int8
	inline hopp::int8 & operator /=(hopp::int8 & a, hopp::int8 const b)
	{
		a = a / b;
		return a;
	}
	/// @brief Operator /= between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return a /= b
	/// @relates hopp::int8
	inline hopp::int8 & operator /=(hopp::int8 & a, int const b)
	{
		a = a / b;
		return a;
	}
	/// @brief Operator /= between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return a /= b
	/// @relates hopp::int8
	inline int & operator /=(int & a, hopp::int8 const b)
	{
		a = a / b;
		return a;
	}
	
	// ==, !=, <, >, <=, >=
	
	/// @brief Operator == between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return true if the hopp::int8 are equal, false otherwise
	/// @relates hopp::int8
	inline bool operator ==(hopp::int8 const a, hopp::int8 const b)
	{
		return a.i == b.i;
	}
	/// @brief Operator == between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return true if the hopp::int8 and the int are equal, false otherwise
	/// @relates hopp::int8
	inline bool operator ==(hopp::int8 const a, int const b)
	{
		return int(a.i) == b;
	}
	/// @brief Operator == between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return true if the int and the hopp::int8 are equal, false otherwise
	/// @relates hopp::int8
	inline bool operator ==(int const a, hopp::int8 const b)
	{
		return a == int(b.i);
	}
	
	/// @brief Operator != between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return true if the hopp::int8 are different, false otherwise
	/// @relates hopp::int8
	inline bool operator !=(hopp::int8 const a, hopp::int8 const b)
	{
		return a.i != b.i;
	}
	/// @brief Operator != between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return true if the hopp::int8 and the int are different, false otherwise
	/// @relates hopp::int8
	inline bool operator !=(hopp::int8 const a, int const b)
	{
		return int(a.i) != b;
	}
	/// @brief Operator != between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return true if the int and the hopp::int8 are different, false otherwise
	/// @relates hopp::int8
	inline bool operator !=(int const a, hopp::int8 const b)
	{
		return a != int(b.i);
	}
	
	/// @brief Operator < between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return true if a < b, false otherwise
	/// @relates hopp::int8
	inline bool operator <(hopp::int8 const a, hopp::int8 const b)
	{
		return a.i < b.i;
	}
	/// @brief Operator < between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return true if a < b, false otherwise
	/// @relates hopp::int8
	inline bool operator <(hopp::int8 const a, int const b)
	{
		return int(a.i) < b;
	}
	/// @brief Operator < between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return true if a < b, false otherwise
	/// @relates hopp::int8
	inline bool operator <(int const a, hopp::int8 const b)
	{
		return a < int(b.i);
	}
	
	/// @brief Operator > between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return true if a > b, false otherwise
	/// @relates hopp::int8
	inline bool operator >(hopp::int8 const a, hopp::int8 const b)
	{
		return a.i > b.i;
	}
	/// @brief Operator > between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return true if a > b, false otherwise
	/// @relates hopp::int8
	inline bool operator >(hopp::int8 const a, int const b)
	{
		return int(a.i) > b;
	}
	/// @brief Operator > between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return true if a > b, false otherwise
	/// @relates hopp::int8
	inline bool operator >(int const a, hopp::int8 const b)
	{
		return a > int(b.i);
	}
	
	/// @brief Operator <= between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return true if a <= b, false otherwise
	/// @relates hopp::int8
	inline bool operator <=(hopp::int8 const a, hopp::int8 const b)
	{
		return a.i <= b.i;
	}
	/// @brief Operator <= between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return true if a <= b, false otherwise
	/// @relates hopp::int8
	inline bool operator <=(hopp::int8 const a, int const b)
	{
		return int(a.i) <= b;
	}
	/// @brief Operator <= between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return true if a <= b, false otherwise
	/// @relates hopp::int8
	inline bool operator <=(int const a, hopp::int8 const b)
	{
		return a <= int(b.i);
	}
	
	/// @brief Operator > between two hopp::int8
	/// @param[in] a A hopp::int8
	/// @param[in] b A hopp::int8
	/// @return true if a >= b, false otherwise
	/// @relates hopp::int8
	inline bool operator >=(hopp::int8 const a, hopp::int8 const b)
	{
		return a.i >= b.i;
	}
	/// @brief Operator > between a hopp::int8 and an int
	/// @param[in] a A hopp::int8
	/// @param[in] b An int
	/// @return true if a >= b, false otherwisev
	inline bool operator >=(hopp::int8 const a, int const b)
	{
		return int(a.i) >= b;
	}
	/// @brief Operator > between an int and a hopp::int8
	/// @param[in] a An int
	/// @param[in] b A hopp::int8
	/// @return true if a >= b, false otherwise
	/// @relates hopp::int8
	inline bool operator >=(int const a, hopp::int8 const b)
	{
		return a >= int(b.i);
	}
	
	// <<, >>
	
	/// @brief Operator << between a std::ostream and a hopp::int8
	/// @param[in,out] o    Output stream
	/// @param[in]     int8 A hopp::int8
	/// @return the output stream
	/// @relates hopp::int8
	inline std::ostream & operator <<(std::ostream & o, hopp::int8 const int8)
	{
		o << static_cast<int>(int8.i);
		return o;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::int8
	/// @param[in,out] i    Input stream
	/// @param[out]    int8 A hopp::int8
	/// @return the output stream
	/// @relates hopp::int8
	inline std::istream & operator >>(std::istream & i, hopp::int8 & int8)
	{
		int tmp;
		i >> tmp;
		int8 = tmp;
		return i;
	}
}

namespace std
{
	/// @brief Specialization of std::numeric_limits<hopp::int8>
	/// @relates hopp::int8
	template <>
	class numeric_limits<hopp::int8>
	{
	public:
		
		// http://en.cppreference.com/w/cpp/types/numeric_limits
		
		/// Identifies types for which std::numeric_limits is specialized 
		static constexpr bool is_specialized = true;
		
		/// Identifies signed types 
		static constexpr bool is_signed = true;
		
		/// Identifies integer types 
		static constexpr bool is_integer = true;
		
		/// Identifies exact types 
		static constexpr bool is_exact = true;
		
		/// Identifies floating-point types that can represent the special value "positive infinity"
		static constexpr bool has_infinity = false;
		
		/// Identifies floating-point types that can represent the special value "signaling not-a-number" (NaN)
		static constexpr bool has_signaling_NaN = false;
		
		/// Identifies the denormalization style used by the floating-point type
		static constexpr bool has_denorm = std::denorm_absent;
		
		/// Identifies the floating-point types that detect loss of precision as denormalization loss rather than inexact result
		static constexpr bool has_denorm_loss = false;
		
		/// Identifies the rounding style used by the type
		static constexpr bool round_style = std::round_toward_zero;
		
		/// Identifies the IEC 559/IEEE 754 floating-point types
		static constexpr bool is_iec559 = false;
		
		/// Identifies the types that represent a finite set of values
		static constexpr bool is_bounded = false;
		
		/// Identifies the types that handle overflows with modulo arithmetic
		static constexpr bool is_modulo = std::numeric_limits<signed char>::is_modulo;
		
		/// Number of radix digits that can be represented without change
		static constexpr int digits = 8 - 1;
		
		/// Number of decimal digits that can be represented without change
		static constexpr int digits10 = std::numeric_limits<signed char>::digits10;
		
		/// Number of decimal digits necessary to differentiate all values of this type
		static constexpr int max_digits10 = 0;
		
		/// The radix or integer base used by the representation of the given type
		static constexpr int radix = 2;
		
		/// One more than the smallest negative power of the radix that is a valid normalized floating-point value
		static constexpr int min_exponent = 0;
		
		/// The smallest negative power of ten that is a valid normalized floating-point value
		static constexpr int min_exponent10 = 0;
		
		/// One more than the largest integer power of the radix that is a valid finite floating-point value
		static constexpr int max_exponent = 0;
		
		/// The largest integer power of 10 that is a valid finite floating-point value
		static constexpr int max_exponent10 = 0;
		
		/// Identifies types which can cause arithmetic operations to trap
		static constexpr bool traps = std::numeric_limits<char>::traps;
		
		/// Identifies floating-point types that detect tinyness before rounding
		static constexpr bool tinyness_before = false;
		
	public:
		
		/// @brief Returns the smallest finite value of the given type
		/// @return the smallest finite value of the given type
		static hopp::int8 min() { return -128; }
		
		/// @brief Returns the lowest finite value of the given type
		/// @return the lowest finite value of the given type
		static hopp::int8 lowest() { return -128; }
		
		/// @brief Returns the largest finite value of the given type
		/// @return the largest finite value of the given type
		static hopp::int8 max() { return 127; }
		
		/// @brief Returns the difference between 1.0 and the next representable value of the given floating-point type
		/// @return the difference between 1.0 and the next representable value of the given floating-point type
		static hopp::int8 epsilon() { return 0; }
		
		/// @brief Returns the maximum rounding error of the given floating-point type
		/// @return the maximum rounding error of the given floating-point type
		static hopp::int8 round_error() { return 0; }
		
		/// @brief Returns the positive infinity value of the given floating-point type
		/// @return the positive infinity value of the given floating-point type
		static hopp::int8 infinity() { return 0; }
		
		/// @brief Returns a quiet NaN value of the given floating-point type
		/// @return a quiet NaN value of the given floating-point type
		static hopp::int8 quiet_NaN() { return 0; }
		
		/// @brief Returns a signaling NaN value of the given floating-point type
		/// @return a signaling NaN value of the given floating-point type
		static hopp::int8 signaling_NaN() { return 0; }
		
		/// @brief Returns the smallest positive subnormal value of the given floating-point type
		/// @return the smallest positive subnormal value of the given floating-point type
		static hopp::int8 denorm_min() { return 0; }
	};
}

#endif
