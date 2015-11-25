// Copyright © 2012-2015 Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_CONTAINER_TREE_HPP
#define HOPP_CONTAINER_TREE_HPP

#include <iostream>
#include <vector>

#include "vector_view.hpp"
#include "../type/is_iterator.hpp"


namespace hopp
{
	// Node
	
	/**
	 * @brief Node for tree
	 *
	 * @code
	   #include <hopp/container/tree.hpp>
	   @endcode
	 *
	 * @ingroup hopp_container
	 */
	template <class T>
	class node
	{
	private:
		
		/// Data
		T m_data;
		
		/// Children
		std::vector<hopp::node<T>> m_children;
		
		/// Father
		hopp::view_ptr<hopp::node<T>> m_father;
		
	public:
		
		/// @brief Constructor
		node(T const & data = T()) :
			m_data(data),
			m_children(),
			m_father(nullptr)
		{ }
		
		/// @brief Get children
		/// @return children
		std::vector<hopp::node<T>> const & children() const { return m_children; }
		
		/// @brief Get children
		/// @return children
		std::vector<hopp::node<T>> & children() { return m_children; }
		
		/// @brief Get father
		/// @return father
		hopp::node<T> const & father() const { return *m_father; }
		
		/// @brief Get father
		/// @return father
		hopp::node<T> & father() { return *m_father; }
	};
	
	/// @brief Operator << between a std::ostream and a hopp::node<T>
	/// @param[in,out] out  A std::ostream
	/// @param[in]     node A hopp::node<T>
	/// @return out
	/// @relates hopp::node
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::node<T> const & node)
	{
		// TODO
		return out;
	}
	
	/// @brief Operator == between two hopp::node<T>
	/// @param[in] a A hopp::node<T>
	/// @param[in] b A hopp::node<T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::node
	template <class T>
	bool operator ==(hopp::node<T> const & a, hopp::node<T> const & b)
	{
		// TODO
		return false;
	}
	
	/// @brief Operator != between two hopp::node<T>
	/// @param[in] a A hopp::node<T>
	/// @param[in] b A hopp::node<T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::node
	template <class T>
	bool operator !=(hopp::node<T> const & a, hopp::node<T> const & b)
	{
		// TODO
		return false;
	}
	
	// Tree
	
	/**
	 * @brief Node for tree
	 *
	 * @code
	   #include <hopp/container/tree.hpp>
	   @endcode
	 *
	 * @ingroup hopp_container
	 */
	template <class T>
	class tree
	{
	public:
		
		/// Value type
		using value_type = T;
		
		/// Const reference type
		using const_reference = T const &;
		
		/// Reference type
		using reference = T &;
		
		/// Const pointer type
		using const_pointer = T const *;
		
		/// Pointer type
		using pointer = T *;
		
		/// Const iterator type
		using const_iterator = typename rows_t::const_iterator;
		
		/// Iterator type
		using iterator = typename rows_t::iterator;
		
		/// Const reverse iterator type
		using const_reverse_iterator = typename rows_t::const_reverse_iterator;
		
		/// Reverse iterator type
		using reverse_iterator = typename rows_t::reverse_iterator;
		
		/// Difference type
		using difference_type = ptrdiff_t;
		
		/// Size type
		using size_type = size_t;
		
	private:
		
		/// Nodes
		std::vector<hopp::node<T>> nodes;
		
	public:
		
		/// @brief Constructor
		/// @param[in] size          Size (0 by default)
		/// @param[in] default_value Default value (T() by default)
		tree(size_t const size = 0u, T const & default_value = T()) :
			nodes(size, default_value)
		{ }
		
		/// @brief Constructor from iterators
		/// @param[in] first Iterator to the first element
		/// @param[in] last  Iterator to the last element (not included)
		template <class input_iterator_t>
		tree(input_iterator_t const & first, input_iterator_t const & last) :
			nodes(first, last)
		{
			static_assert(hopp::is_iterator<input_iterator_t>::value, "hopp::tree<T>::tree:  error: input_iterator_t is not an iterator");
		}
	};
	
	/// @brief Operator << between a std::ostream and a hopp::tree<T>
	/// @param[in,out] out  A std::ostream
	/// @param[in]     tree A hopp::tree<T>
	/// @return out
	/// @relates hopp::tree
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::tree<T> const & tree)
	{
		// TODO
		return out;
	}
	
	/// @brief Operator == between two hopp::tree<T>
	/// @param[in] a A hopp::tree<T>
	/// @param[in] b A hopp::tree<T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::tree
	template <class T>
	bool operator ==(hopp::tree<T> const & a, hopp::tree<T> const & b)
	{
		// TODO
		return false;
	}
	
	/// @brief Operator != between two hopp::tree<T>
	/// @param[in] a A hopp::tree<T>
	/// @param[in] b A hopp::tree<T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::tree
	template <class T>
	bool operator !=(hopp::tree<T> const & a, hopp::tree<T> const & b)
	{
		// TODO
		return false;
	}
}

#endif
