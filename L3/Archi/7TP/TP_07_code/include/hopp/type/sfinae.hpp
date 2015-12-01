// Copyright © 2013-2015 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_TYPE_SFINAE_HPP
#define HOPP_TYPE_SFINAE_HPP

#include <type_traits>


namespace hopp
{
	// http://stackoverflow.com/questions/9530928/checking-a-member-exists-possibly-in-a-base-class-c11-version
	
	/**
	 * @brief hopp::this_type<T>::is_valid (SFINAE)
	 *
	 * In a partial template specialization, you can check if the type is valid:
	 * @code
	   template <class T, typename hopp::this_type<your_type>::is_valid>
	   class
	   {
	   	// ...
	   };
	   @endcode
	 * 
	 * For example (see hopp/memory/clone.hpp), you can check is a type has the .clone() member function:
	 * @code
	   // Valid fonctor (return false) for all types
	   template <class T, class sfinae_valid_type = void>
	   class is_cloneable : public std::false_type
	   { };
	   
	   // This partial template specialization fonctor (return true) is created only if
	   // the type "decltype(std::declval<T &>().clone())" is valid i.e. T::clone() exists
	   template <class T>
	   class is_cloneable<T, typename hopp::this_type<decltype(std::declval<T &>().clone())>::is_valid> : public std::true_type
	   { };
	   @endcode
	 *
	 * @ingroup hopp_type
	 */
	template <class>
	struct this_type
	{
		/// is_valid type
		using is_valid = void;
		
		/// is_not_void type
		using is_not_void = void;
	};
	
	template <>
	struct this_type<void>
	{
		/// is_valid type
		using is_valid = void;
		
		/// is_void type
		using is_void = void;
	};
	
	// http://en.cppreference.com/w/cpp/types/enable_if
	
	/// @brief hopp::this_expr<T>::is_true or hopp::this_expr<T>::is_false (SFINAE)
	/// @ingroup hopp_type
	template <bool b>
	struct this_expr { };
	
	/// @brief hopp::this_expr<T>::is_true (SFINAE)
	/// @ingroup hopp_type
	template <>
	struct this_expr<true>
	{
		/// is_true type
		using is_true = void;
	};
	
	/// @brief hopp::this_expr<T>::is_false (SFINAE)
	/// @ingroup hopp_type
	template <>
	struct this_expr<false>
	{
		/// is_false type
		using is_false = void;
	};
}

#endif
