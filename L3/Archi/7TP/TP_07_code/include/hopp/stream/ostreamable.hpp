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


#ifndef HOPP_STREAM_OSTREAMABLE_HPP
#define HOPP_STREAM_OSTREAMABLE_HPP

#include <iostream>
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


namespace hopp
{
	/// @brief Wrapper to display objects with std::ostream
	/// @ingroup hopp_stream
	template <class T>
	class ostreamable_t
	{
	public:
		
		/// Object
		T const & t;
		
		/// @brief Constructor
		/// @param[in] t An object
		ostreamable_t(T const & t) : t(t) { }
	};
	
	/// @brief Create a hopp::ostreamable_t<T>
	/// @param[in] t An object
	/// @relates hopp::ostreamable_t
	template <class T>
	hopp::ostreamable_t<T> ostreamable(T const & t)
	{
		return hopp::ostreamable_t<T>(t);
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<T>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<T>
	/// @return the output stream
	/// @relates hopp::ostreamable_t
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<T> const & ostreamable)
	{
		out << ostreamable.t;
		return out;
	}
	
	namespace
	{
		// Print a std container like std::vector, std::list or std::set
		template <class container_t>
		void print_container(std::ostream & out, container_t const & container)
		{
			out << "{";
			for (auto const & e : container)
			{
				if (&e == &*container.begin()) { out << " "; }
				else { out << ", "; }
				
				out << hopp::ostreamable(e);
			}
			out << " }";
		}
		
		// Print a std container like std::map
		template <class map_t>
		void print_map(std::ostream & out, map_t const & map)
		{
			out << "{";
			for (auto const & key_value : map)
			{
				auto const & key = key_value.first;
				auto const & value = key_value.second;
				
				if (&key_value != &*map.begin()) { out << ","; }
				out << " " << hopp::ostreamable(key) << ": " << hopp::ostreamable(value);
			}
			out << " " << "}";
		}
		
		// Print a std container like std::tuple
		template <size_t i, class tuple_t>
		class print_tuple_t
		{
		public:
			void operator ()(std::ostream & out, tuple_t const & tuple)
			{
				hopp::print_tuple_t<i - 1, tuple_t>()(out, tuple);
				out << " " << hopp::ostreamable(std::get<i>(tuple));
			}
		};
		// Specialization
		template <class tuple_t>
		class print_tuple_t<0, tuple_t>
		{
		public:
			void operator ()(std::ostream & out, tuple_t const & tuple)
			{
				out << " " << hopp::ostreamable(std::get<0>(tuple));
			}
		};
		
		// Print a std container like std::tuple
		template <class ... args_t, template <class ...> class tuple_t>
		void print_tuple(std::ostream & out, tuple_t<args_t ...> const & tuple)
		{
			out << "{";
			hopp::print_tuple_t<sizeof...(args_t) - 1, tuple_t<args_t ...>>()(out, tuple);
			out << " " << "}";
		}
	}
	
	// std::vector, std::list, ...
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::vector<T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::vector<T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::vector<T>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::list<T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::list<T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::list<T>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::forward_list<T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::forward_list<T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::forward_list<T>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::deque<T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::deque<T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::deque<T>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::stack<T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::stack<T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::stack<T>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::queue<T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::queue<T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::queue<T>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::priority_queue<T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::priority_queue<T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::priority_queue<T>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	// std::array
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::array<T, N>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::array<T, N>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T, size_t N>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::array<T, N>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	// std::set
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::set<T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::set<T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::set<T>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::multiset<T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::multiset<T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::multiset<T>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::unordered_set<T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::unordered_set<T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::unordered_set<T>> const & ostreamable)
	{
		hopp::print_container(out, ostreamable.t);
		return out;
	}
	
	// std::map
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::map<key_t, T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::map<key_t, T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class key_t, class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::map<key_t, T>> const & ostreamable)
	{
		hopp::print_map(out, ostreamable.t);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::multimap<key_t, T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::multimap<key_t, T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class key_t, class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::multimap<key_t, T>> const & ostreamable)
	{
		hopp::print_map(out, ostreamable.t);
		return out;
	}
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::unordered_map<key_t, T>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::unordered_map<key_t, T>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class key_t, class T>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::unordered_map<key_t, T>> const & ostreamable)
	{
		hopp::print_map(out, ostreamable.t);
		return out;
	}
	
	// std::tuple
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::tuple<args_t ...>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::tuple<args_t ...>>
	/// @return the output stream
	template <class ... args_t>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::tuple<args_t ...>> const & ostreamable)
	{
		hopp::print_tuple(out, ostreamable.t);
		return out;
	}
	
	// std::pair
	
	/// @brief Operator << between a std::ostream and a hopp::ostreamable_t<std::pair<T0, T1>>
	/// @param[in,out] out         Output stream
	/// @param[in]     ostreamable A hopp::ostreamable_t<std::pair<T0, T1>>
	/// @return the output stream
	/// @ingroup hopp_stream
	template <class T0, class T1>
	std::ostream & operator <<(std::ostream & out, hopp::ostreamable_t<std::pair<T0, T1>> const & ostreamable)
	{
		out << "{ " << hopp::ostreamable(ostreamable.t.first) << ", " << hopp::ostreamable(ostreamable.t.second) << " }";
		return out;
	}
}

#endif
