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


#ifndef HOPP_TYPE_IS_ITERATOR_HPP
#define HOPP_TYPE_IS_ITERATOR_HPP

#include <iterator>

#include "sfinae.hpp"


namespace hopp
{
	// http://stackoverflow.com/questions/12032771/how-to-check-if-an-arbitrary-type-is-an-iterator/12032923#12032923
	
	// is_iterator
	
	/// @brief Is iterator?
	/// @ingroup hopp_type
	template <class T, class = void>
	struct is_iterator : public std::false_type
	{
		/// no type
		using no = void;
	};
	
	/// @brief Is iterator? (specialization of hopp::is_iterator<T>)
	/// @ingroup hopp_type
	template <class T>
	struct is_iterator
	<
		T,
		typename hopp::this_type<typename std::iterator_traits<T>::value_type>::is_not_void
	> :
		public std::true_type
	{
		/// yes type
		using yes = void;
	};
}

#endif
