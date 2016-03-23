// Copyright © 2015 Rodolphe Cargnello, rodolphe.cargnello@gmail.com
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


#ifndef HOPP_CONTAINER_VECTOR_PAIR_HPP
#define HOPP_CONTAINER_VECTOR_PAIR_HPP

#include <iostream>
#include <stdexcept>
#include <vector>
#include <cstddef>
#include <algorithm>

#include "../conversion/to_string.hpp"
#include "../stream/ostreamable.hpp"
#include "../type/is_iterator.hpp"


namespace hopp
{
	/**
	 * @brief Associative container that contains key-value pairs
	 *
	 * @code
	   #include <hopp/container.hpp>
	   @endcode
	 *
	 * Example:
	 * @code
	   hopp::vector_pair<std::string, int> pairs;
	   
	   pairs["one"] = 1; // Create "one" key with 1 value
	   pairs["two"] = 2;
	   pairs["three"] = 4;
	   pairs["three"] = 3; // Replace value at key "three"
	   
	   std::cout << pairs << std::endl; // { { one, 1 }, { two, 2 }, { three, 3 } }
	   @endcode
	 *
	 * @ingroup hopp_container
	 */
	template <class key_t, class T>
	class vector_pair
	{
	public:
		
		/// Key type
		using key_type = key_t;
		
		/// Mapped type
		using mapped_type = T;
		
		/// Value type
		using value_type = typename std::pair<key_t, T>;
		
		/// Const reference type
		using const_reference = value_type const &;
		
		/// Reference type
		using reference = value_type &;
		
		/// Const pointer type
		using const_pointer = value_type const *;
		
		/// Pointer type
		using pointer = value_type *;
		
		/// Const iterator type
		using const_iterator = typename std::vector<value_type>::const_iterator;
		
		/// Iterator type
		using iterator = typename std::vector<value_type>::iterator;
		
		/// Const reverse iterator type
		using const_reverse_iterator = typename std::vector<value_type>::const_reverse_iterator;
		
		/// Reverse iterator type
		using reverse_iterator = typename std::vector<value_type>::reverse_iterator;
		
		/// Difference type
		using difference_type = ptrdiff_t;
		
		/// Size type
		using size_type = size_t;
		
	private:
		
		/// Vector of pairs (keys and values)
		std::vector<std::pair<key_t, T>> m_pairs;
		
	public:
		
		/// @brief Default constructor
		vector_pair() = default;
		
		/// @brief Constructor from std::vector<std::pair<key_t, T>>
		/// @param[in] pairs A std::vector<std::pair<key_t, T>>
		vector_pair(std::vector<std::pair<key_t, T>> const & pairs) :
			hopp::vector_pair<key_t, T>(std::begin(pairs), std::end(pairs))
		{ }
		
		/// @brief Constructor from std::initializer_list<std::pair<key_t, T>>
		/// @param[in] first Iterator to the first element
		/// @param[in] last  Iterator to the last element (not included)
		vector_pair(std::initializer_list<std::pair<key_t, T>> const & initializer_list) :
			hopp::vector_pair<key_t, T>(std::begin(initializer_list), std::end(initializer_list))
		{ }
		
		/// @brief Constructor from iterators
		/// @param[in] first Iterator to the first element
		/// @param[in] last  Iterator to the last element (not included)
		template <class input_iterator_t>
		vector_pair(input_iterator_t const & first, input_iterator_t const & last) :
			m_pairs()
		{
			static_assert(hopp::is_iterator<input_iterator_t>::value, "hopp::vector_pair<key_t, T>::vector_pair:  error: input_iterator_t is not an iterator");
			
			for (auto it = first; it != last; ++it)
			{
				push_back(it->first, it->second);
			}
		}
		
		// Data
		
		/// @brief Pairs values access
		/// @return A std::vector<std::pair<key_t, T>>
		std::vector<std::pair<key_t, T>> const & data() const { return m_pairs; }
		
		/// @brief Pairs values access
		/// @return A std::vector<std::pair<key_t, T>>
		std::vector<std::pair<key_t, T>> & data() { return m_pairs; }
		
		// Size
		
		/// @brief Is empty?
		/// @return true if the vector_pair is empty, false otherwise
		bool empty() const { return m_pairs.empty(); }
		
		/// @brief Size
		/// @return the size
		size_t size() const { return m_pairs.size(); }
		
		/// @brief Capacity
		/// @return the capacity
		size_t capacity() const { return m_pairs.capacity(); }
		
		/// @brief Maximum size
		/// @return the maximum size
		size_t max_size() const { return m_pairs.max_size(); }
		
		// Find
		
		/// @brief Find element with a key
		/// @param[in] key A key
		/// @return the iterator the element found, end iterator if not found
		const_iterator find(key_t const & key) const
		{
			return std::find_if(m_pairs.cbegin(), m_pairs.cend(), [&key](value_type const & pair) -> bool { return pair.first == key; });
		}
		
		/// @brief Find element with a key
		/// @param[in] key A key
		/// @return the iterator the element found, end iterator if not found
		iterator find(key_t const & key)
		{
			return std::find_if(m_pairs.begin(), m_pairs.end(), [&key](value_type const & pair) -> bool { return pair.first == key; });
		}
		
		// Access
		
		/// @brief Value access
		/// @param[in] key A key
		/// @return the value at key
		/// @exception std::out_of_range if key does not exist
		T const & at(key_t const & key) const
		{
			auto const it = find(key);
			
			if (it == m_pairs.cend())
			{
				throw std::out_of_range("hopp::vector_pair<key_t, values_t>:at: invalid key \"" + hopp::to_string(key) + "\"");
			}
			return it->second;
		}
		
		/// @brief Value access
		/// @param[in] key A key
		/// @return the value at key
		/// @exception std::out_of_range if key does not exist
		T & at(key_t const & key)
		{
			auto const it = find(key);
			
			if (it == m_pairs.cend())
			{
				throw std::out_of_range("hopp::vector_pair<key_t, values_t>:at: invalid key \"" + hopp::to_string(key) + "\"");
			}
			return it->second;
		}
		
		/// @brief Value access (create the key if it does not exist)
		/// @param[in] key A key
		/// @return the value at key (create the key if it does not exist)
		T & operator [](key_t const & key)
		{
			auto it = find(key);
			
			if (it == m_pairs.end()) { it = insert(key, T()); }
			
			return it->second;
		}
		
		/// @brief Access to the first element
		/// @return the first element
		/// @pre The vector_pair is not empty
		std::pair<key_t, T> const & front() const { return m_pairs.front(); }
		
		/// @brief Access to the first element
		/// @return the first element
		/// @pre The vector_pair is not empty
		std::pair<key_t, T> & front() { return m_pairs.front(); }
		
		/// @brief Access to the last element
		/// @return the last element
		/// @pre The vector_pair is not empty
		std::pair<key_t, T> const & back() const { return m_pairs.back(); }
		
		/// @brief Access to the last element
		/// @return the last element
		/// @pre The vector_pair is not empty
		std::pair<key_t, T> & back() { return m_pairs.back(); }
		
		// emplace_back, push_back, insert, erase & clear
		
		/// @brief Add an element at the end
		/// @param[in] key   A key
		/// @param[in] value A value
		void emplace_back(key_t const & key, T const & value) { insert(key, value); }
		
		/// @brief Add an element at the end
		/// @param[in] key_value A key and a value
		void push_back(std::pair<key_t, T> const & key_value) { insert(key_value); }
		
		/// @brief Add an element at the end
		/// @param[in] key   A key
		/// @param[in] value A value
		void push_back(key_t const & key, T const & value) { insert(key, value); }
		
		/// @brief Add an element at the end
		/// @param[in] key_value A key and a value
		/// @return a iterator to the element inserted
		iterator insert(std::pair<key_t, T> const & key_value)
		{
			return insert(key_value.first, key_value.second);
		}
		
		/// @brief Add an element at the end
		/// @param[in] key   A key
		/// @param[in] value A value
		/// @return a iterator to the element inserted
		iterator insert(key_t const & key, T const & value)
		{
			auto const it = find(key);
			
			if (it != m_pairs.end())
			{
				it->second = value;
				return it;
			}
			else
			{
				m_pairs.emplace_back(key, value);
				return --m_pairs.end();
			}
		}
		
		/// @brief Erase an element
		/// @param Key A key
		/// @return an iterator pointing to the new location of the element that followed the last element erased by the function call
		/// @pre the key is valid
		iterator erase(key_t const & key)
		{
			auto const it = find(key);
			return erase(it);
		}
		
		/// @brief Erase an element
		/// @param it An iterator
		/// @return an iterator pointing to the new location of the element that followed the last element erased by the function call
		/// @pre the iterator is valid
		iterator erase(const_iterator const & it)
		{
			return m_pairs.erase(it);
		}
		
		/// @brief Erase elements between two iterators
		/// @param[in] first Iterator to the first element
		/// @param[in] last  Iterator to the last element (not included)
		/// @return an iterator pointing to the new location of the element that followed the last element erased by the function call
		/// @pre the iterators are valid
		iterator erase(const_iterator const & first, const_iterator const & last)
		{
			return m_pairs.erase(first, last);
		}
		
		/// @brief Remove all elements
		void clear() { m_pairs.clear(); }
		
		// Iterator
		
		/// @brief Get const iterator to beginning
		/// @return const iterator to beginning
		const_iterator begin() const { return m_pairs.begin(); }
		
		/// @brief Get const iterator to beginning
		/// @return const iterator to beginning
		const_iterator cbegin() const { return m_pairs.cbegin(); }
		
		/// @brief Get iterator to beginning
		/// @return iterator to beginning
		iterator begin() { return m_pairs.begin(); }
		
		/// @brief Get const iterator to end
		/// @return const iterator to end
		const_iterator end() const { return m_pairs.end(); }
		
		/// @brief Get const iterator to end
		/// @return const iterator to end
		const_iterator cend() const { return m_pairs.cend(); }
		
		/// @brief Get iterator to end
		/// @return iterator to end
		iterator end() { return m_pairs.end(); }
		
		// Reverse iterator
		
		/// @brief Get const reverse iterator to reverse beginning
		/// @return const reverse iterator to reverse beginning
		const_reverse_iterator rbegin() const { return m_pairs.rbegin(); }
		
		/// @brief Get const reverse iterator to reverse beginning
		/// @return const reverse iterator to reverse beginning
		const_reverse_iterator crbegin() const { return m_pairs.crbegin(); }
		
		/// @brief Get reverse iterator to reverse beginning
		/// @return reverse iterator to reverse beginning
		reverse_iterator bregin() { return m_pairs.rbegin(); }
		
		/// @brief Get const reverse iterator to reverse end
		/// @return const reverse iterator to reverse end
		const_reverse_iterator rend() const { return m_pairs.rend(); }
		
		/// @brief Get const reverse iterator to reverse end
		/// @return const reverse iterator to reverse end
		const_reverse_iterator crend() const { return m_pairs.crend(); }
		
		/// @brief Get reverse iterator to reverse end
		/// @return reverse iterator to reverse end
		reverse_iterator rend() { return m_pairs.rend(); }
	};
	
	/// @brief Operator << between a std::ostream and a hopp::vector_pair<key_t, T>
	/// @param[in,out] out      A std::ostream
	/// @param[in]     vector_pair A hopp::vector_pair<key_t, T>
	/// @return out
	/// @relates hopp::vector_pair
	template <class key_t, class T>
	std::ostream & operator <<(std::ostream & out, hopp::vector_pair<key_t, T> const & vector_pair)
	{
		out << hopp::ostreamable(vector_pair.data());
		return out;
	}
	
	/// @brief Operator == between two hopp::vector_pair<key_t, T>
	/// @param[in] a A hopp::vector_pair<key_t, T>
	/// @param[in] b A hopp::vector_pair<key_t, T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::vector_pair
	template <class key_t, class T>
	bool operator ==(hopp::vector_pair<key_t, T> const & a, hopp::vector_pair<key_t, T> const & b)
	{
		return a.data() == b.data();
	}
	
	/// @brief Operator != between two hopp::vector_pair<key_t, T>
	/// @param[in] a A hopp::vector_pair<key_t, T>
	/// @param[in] b A hopp::vector_pair<key_t, T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::vector_pair
	template <class key_t, class T>
	bool operator !=(hopp::vector_pair<key_t, T> const & a, hopp::vector_pair<key_t, T> const & b)
	{
		return (a == b) == false;
	}
}

#endif
 
