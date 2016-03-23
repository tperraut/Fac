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


#ifndef HOPP_PRINT_STD_HPP
#define HOPP_PRINT_STD_HPP

#include <vector>
#include <list>
#include <forward_list>
#include <deque>
#include <stack>
#include <queue>
#include <set>
#include <unordered_set>
#include <map>
#include <unordered_map>

#include "../stream/ostreamable.hpp"


namespace std
{
	// std::vector, std::list, ...
	
	/// @brief Operator << between a std::ostream and a std::vector
	/// @param[in,out] out    Output stream
	/// @param[in]     vector A std::vector
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T>
	std::ostream & operator <<(std::ostream & out, std::vector<T> const & vector)
	{
		hopp::print_container(out, vector);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a std::list
	/// @param[in,out] out  Output stream
	/// @param[in]     list A std::list
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T>
	std::ostream & operator <<(std::ostream & out, std::list<T> const & list)
	{
		hopp::print_container(out, list);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a std::forward_list
	/// @param[in,out] out  Output stream
	/// @param[in]     list A std::forward_list
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T>
	std::ostream & operator <<(std::ostream & out, std::forward_list<T> const & list)
	{
		hopp::print_container(out, list);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a std::deque
	/// @param[in,out] out   Output stream
	/// @param[in]     deque A std::deque
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T>
	std::ostream & operator <<(std::ostream & out, std::deque<T> const & deque)
	{
		hopp::print_container(out, deque);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a std::stack
	/// @param[in,out] out   Output stream
	/// @param[in]     stack A std::stack
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T>
	std::ostream & operator <<(std::ostream & out, std::stack<T> const & stack)
	{
		hopp::print_container(out, stack);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a std::queue
	/// @param[in,out] out   Output stream
	/// @param[in]     queue A std::queue
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T>
	std::ostream & operator <<(std::ostream & out, std::queue<T> const & queue)
	{
		hopp::print_container(out, queue);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a std::priority_queue
	/// @param[in,out] out   Output stream
	/// @param[in]     queue A std::priority_queue
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T>
	std::ostream & operator <<(std::ostream & out, std::priority_queue<T> const & queue)
	{
		hopp::print_container(out, queue);
		return out;
	}
	
	// std::array
	
	/// @brief Operator << between a std::ostream and a std::array
	/// @param[in,out] out   Output stream
	/// @param[in]     array A std::array
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T, size_t N>
	std::ostream & operator <<(std::ostream & out, std::array<T, N> const & array)
	{
		hopp::print_container(out, array);
		return out;
	}
	
	// std::set
	
	/// @brief Operator << between a std::ostream and a std::set
	/// @param[in,out] out Output stream
	/// @param[in]     set A std::set
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T>
	std::ostream & operator <<(std::ostream & out, std::set<T> const & set)
	{
		hopp::print_container(out, set);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a std::multiset
	/// @param[in,out] out Output stream
	/// @param[in]     set A std::multiset
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T>
	std::ostream & operator <<(std::ostream & out, std::multiset<T> const & set)
	{
		hopp::print_container(out, set);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a std::unordered_set
	/// @param[in,out] out Output stream
	/// @param[in]     set A std::unordered_set
	/// @return the output stream
	/// @ingroup hopp_print
	template <class T>
	std::ostream & operator <<(std::ostream & out, std::unordered_set<T> const & set)
	{
		hopp::print_container(out, set);
		return out;
	}
	
	// std::map
	
	/// @brief Operator << between a std::ostream and a std::map
	/// @param[in,out] out Output stream
	/// @param[in]     map A std::map
	/// @return the output stream
	/// @ingroup hopp_print
	template <class key_t, class T>
	std::ostream & operator <<(std::ostream & out, std::map<key_t, T> const & map)
	{
		hopp::print_map(out, map);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a std::multimap
	/// @param[in,out] out Output stream
	/// @param[in]     map A std::multimap
	/// @return the output stream
	/// @ingroup hopp_print
	template <class key_t, class T>
	std::ostream & operator <<(std::ostream & out, std::multimap<key_t, T> const & map)
	{
		hopp::print_map(out, map);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a std::unordered_map
	/// @param[in,out] out Output stream
	/// @param[in]     map A std::unordered_map
	/// @return the output stream
	/// @ingroup hopp_print
	template <class key_t, class T>
	std::ostream & operator <<(std::ostream & out, std::unordered_map<key_t, T> const & map)
	{
		hopp::print_map(out, map);
		return out;
	}
	
	// std::tuple
	
	/// @brief Operator << between a std::ostream and a std::tuple
	/// @param[in,out] out   Output stream
	/// @param[in]     tuple A std::tuple
	/// @return the output stream
	template <class ... args_t>
	std::ostream & operator <<(std::ostream & out, std::tuple<args_t ...> const & tuple)
	{
		hopp::print_tuple(out, tuple);
		return out;
	}
}

#endif
