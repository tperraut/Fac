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


#ifndef HOPP_CONTAINER_VECTOR_VIEW_HPP
#define HOPP_CONTAINER_VECTOR_VIEW_HPP

#include <iostream>
#include <stdexcept>

#include "../memory/view_ptr.hpp"


namespace hopp
{
	/**
	 * @brief Vector view
	 *
	 * @code
	   #include <hopp/container/vector_view.hpp>
	   @endcode
	 *
	 * @ingroup hopp_container
	 */
	template <class T>
	class vector_view
	{
	public:
		
		/// Value type
		using value_type = typename T::value_type;
		
		/// Const reference type
		using const_reference = typename T::const_reference;
		
		/// Reference type
		using reference = typename T::reference;
		
		/// Const pointer type
		using const_pointer = typename T::const_pointer;
		
		/// Pointer type
		using pointer = typename T::pointer;
		
		/// Const iterator type
		using const_iterator = typename T::const_iterator;
		
		/// Iterator type
		using iterator = typename T::iterator;
		
		/// Const reverse iterator type
		using const_reverse_iterator = typename T::const_reverse_iterator;
		
		/// Reverse iterator type
		using reverse_iterator = typename T::reverse_iterator;
		
		/// Difference type
		using difference_type = typename T::difference_type;
		
		/// Size type
		using size_type = typename T::size_type;
		
	private:
		
		/// Reference on vector
		hopp::view_ptr<T> p_vector;
		
		/// Index of the beginning
		size_t m_begin;
		
		/// Index of the end
		size_t m_end;
		
	public:
		
		/// @brief Default constructor
		vector_view() : p_vector(nullptr), m_begin(0), m_end(0) { }
		
		/// @brief Constructor
		/// @param[in] vector  A vector of T
		/// @param[in] i_begin Index of the beginning
		/// @param[in] i_end   Index of the end
		vector_view(T & vector, size_t const i_begin, size_t const i_end) :
			p_vector(vector), m_begin(i_begin), m_end(i_end)
		{ }
		
		// Size, Vector & Data
		
		/// @brief Return the number of rows
		/// @return the number of rows
		size_t size() const { return m_end - m_begin; }
		
		/// @brief Get vector
		/// @return vector
		T const & vector() const { return *p_vector; }
		
		/// @brief Get data
		/// @return data
		T & vector() { return *p_vector; }
		
		/// @brief Get data
		/// @return data
		const_pointer data() const { return p_vector->data(); }
		
		/// @brief Get data
		/// @return data
		pointer data() { return p_vector->data(); }
		
		// Access: operator [i]
		
		/// @brief Const value access
		/// @param i Index
		/// @return value at i
		value_type const & operator [](size_t const i) const { return (*p_vector)[m_begin + i]; }
		
		/// @brief Value access
		/// @param i Index
		/// @return value at i
		value_type & operator [](size_t const i) { return (*p_vector)[m_begin + i]; }
		
		// Access: .at(i)
		
		/// @brief Const safe value access
		/// @param i Index
		/// @return value at i
		/// @exception std::out_of_range if i >= number of values
		value_type const & at(size_t const i) const
		{
			if (m_begin + i >= p_vector->size()) { throw std::out_of_range("hopp::vector_view<T>::at(i): invalid i index"); }
			return (*p_vector)[m_begin + i];
		}
		
		/// @brief Safe value access
		/// @param i Index
		/// @return value at i
		/// @exception std::out_of_range if i >= number of values
		value_type & at(size_t const i)
		{
			if (m_begin + i >= p_vector->size()) { throw std::out_of_range("hopp::vector_view<T>::at(i): invalid i index"); }
			return (*p_vector)[m_begin + i];
		}
		
		// front, back
		
		/// @brief Get first value
		/// @pre Number of values is not zero
		/// @return first value
		value_type const & front() const { return (*p_vector)[m_begin]; }
		
		/// @brief Get first value
		/// @pre Number of values is not zero
		/// @return first value
		value_type & front() { return (*p_vector)[m_begin]; }
		
		/// @brief Get last value
		/// @pre Number of values is not zero
		/// @return last value
		value_type const & back() const { return (*p_vector)[m_end - 1]; }
		
		/// @brief Get last value
		/// @pre Number of values is not zero
		/// @return last value
		value_type & back() { return (*p_vector)[m_end - 1]; }
		
		// Iterator
		
		/// @brief Get const iterator to beginning
		/// @return const iterator to beginning
		const_iterator begin() const { return p_vector->begin() + ptrdiff_t(m_begin); }
		
		/// @brief Get const iterator to beginning
		/// @return const iterator to beginning
		const_iterator cbegin() const { return p_vector->begin() + ptrdiff_t(m_begin); }
		
		/// @brief Get iterator to beginning
		/// @return iterator to beginning
		iterator begin() { return p_vector->begin() + ptrdiff_t(m_begin); }
		
		/// @brief Get const iterator to end
		/// @return const iterator to end
		const_iterator end() const { return p_vector->begin() + ptrdiff_t(m_end); }
		
		/// @brief Get const iterator to end
		/// @return const iterator to end
		const_iterator cend() const { return p_vector->begin() + ptrdiff_t(m_end); }
		
		/// @brief Get iterator to end
		/// @return iterator to end
		iterator end() { return p_vector->begin() + ptrdiff_t(m_end); }
		
		// Reverse iterator
		
		/// @brief Get const reverse iterator to reverse beginning
		/// @return const reverse iterator to reverse beginning
		const_reverse_iterator rbegin() const { return p_vector->rbegin() + ptrdiff_t(m_begin); }
		
		/// @brief Get const reverse iterator to reverse beginning
		/// @return const reverse iterator to reverse beginning
		const_reverse_iterator crbegin() const { return p_vector->rbegin() + ptrdiff_t(m_begin); }
		
		/// @brief Get reverse iterator to reverse beginning
		/// @return reverse iterator to reverse beginning
		reverse_iterator bregin() { return p_vector->rbegin() + ptrdiff_t(m_begin); }
		
		/// @brief Get const reverse iterator to reverse end
		/// @return const reverse iterator to reverse end
		const_reverse_iterator rend() const { return p_vector->rbegin() + ptrdiff_t(m_end); }
		
		/// @brief Get const reverse iterator to reverse end
		/// @return const reverse iterator to reverse end
		const_reverse_iterator crend() const { return p_vector->rbegin() + ptrdiff_t(m_end); }
		
		/// @brief Get reverse iterator to reverse end
		/// @return reverse iterator to reverse end
		reverse_iterator rend() { return p_vector->rbegin() + ptrdiff_t(m_end); }
	};
	
	/// @brief Operator << between a std::ostream and a hopp::vector_view<T>
	/// @param[in,out] out         A std::ostream
	/// @param[in]     vector_view A hopp::vector_view<T>
	/// @return out
	/// @relates hopp::vector_view
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::vector_view<T> const & vector_view)
	{
		out << "{";
		for (size_t i = 0; i < vector_view.size(); ++i)
		{
			if (i == 0) { out << " "; }
			else { out << ", "; }
			
			out << vector_view[i];
		}
		out << " }";
		
		return out;
	}
	
	/// @brief Operator == between two hopp::vector_view<T>
	/// @param[in] a A hopp::vector_view<T>
	/// @param[in] b A hopp::vector_view<T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::vector_view
	template <class T>
	bool operator ==(hopp::vector_view<T> const & a, hopp::vector_view<T> const & b)
	{
		return a.vector() == b.vector();
	}
	
	/// @brief Operator != between two hopp::vector_view<T>
	/// @param[in] a A hopp::vector_view<T>
	/// @param[in] b A hopp::vector_view<T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::vector_view
	template <class T>
	bool operator !=(hopp::vector_view<T> const & a, hopp::vector_view<T> const & b)
	{
		return (a == b) == false;
	}
	
	/// @brief Create a hopp::vector_view<T>
	/// @param[in] vector  A vector
	/// @param[in] i_begin Index of the beginning
	/// @param[in] i_end   Index of the end
	/// @relates hopp::vector_view
	template <class T>
	hopp::vector_view<const T> make_vector_view(T const & vector, size_t const i_begin, size_t const i_end)
	{
		return hopp::vector_view<const T>(vector, i_begin, i_end);
	}
	
	/// @brief Create a hopp::vector_view<T>
	/// @param[in] vector  A vector
	/// @param[in] i_begin Index of the beginning
	/// @param[in] i_end   Index of the end
	/// @relates hopp::vector_view
	template <class T>
	hopp::vector_view<T> make_vector_view(T & vector, size_t const i_begin, size_t const i_end)
	{
		return hopp::vector_view<T>(vector, i_begin, i_end);
	}
}

#endif
