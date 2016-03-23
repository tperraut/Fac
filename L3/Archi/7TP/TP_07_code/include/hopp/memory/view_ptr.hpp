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


#ifndef HOPP_MEMORY_VIEW_PTR_HPP
#define HOPP_MEMORY_VIEW_PTR_HPP

#include <iostream>
#include <cstddef>

#include "../compiler/unused.hpp"


namespace hopp
{
	/**
	 * @brief Like std::reference_wrapper<T> but can be null (nullptr)
	 * @ingroup hopp_memory
	 */
	template <class T>
	class view_ptr
	{
	private:
		
		/// Pointer to object
		T * m_ptr;
		
	public:
		
		/// @brief Default constructor
		view_ptr() : m_ptr(nullptr) { }
		
		/// @brief Constructor from nullptr
		/// @param[in] p nullptr
		view_ptr(std::nullptr_t const p) : m_ptr(p) { }
		
		/// @brief Constructor from T
		/// @param[in] t A T
		view_ptr(T & t) : m_ptr(&t) { }
		
		/// @brief Return the stored pointer
		/// @pre The pointer is not nullptr
		/// @return the stored pointer
		T const & get() const { return *m_ptr; }
		
		/// @brief Return the stored pointer
		/// @pre The pointer is not nullptr
		/// @return the stored pointer
		T & get() { return *m_ptr; }
		
		/// @brief Return true if the pointer is not empty, false otherwise
		/// @return true if the pointer is not empty, false otherwise
		operator bool() const { return m_ptr != nullptr; }
		
		/// @brief Return a reference to the stored object
		/// @pre The pointer is not nullptr
		/// @return a reference to the stored object
		T const & operator *() const { return *m_ptr; }
		
		/// @brief Return a reference to the stored object
		/// @pre The pointer is not nullptr
		/// @return a reference to the stored object
		T & operator *() { return *m_ptr; }
		
		/// @brief Return a reference to the stored object to access of its members
		/// @pre The pointer is not nullptr
		/// @return a reference to the stored object to access of its members
		T const * operator ->() const { return m_ptr; }
		
		/// @brief Return a reference to the stored object to access of its members
		/// @pre The pointer is not nullptr
		/// @return a reference to the stored object to access of its members
		T * operator ->() { return m_ptr; }
	};
	
	/// @brief Operator << between a std::ostream and a hopp::view_ptr<T>
	/// @param[in,out] out      A std::ostream
	/// @param[in]     view_ptr A hopp::view_ptr<T>
	/// @return out
	/// @relates hopp::view_ptr
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::view_ptr<T> const & view_ptr)
	{
		if (view_ptr) { out << *view_ptr; }
		else { out << "nullptr"; }
		return out;
	}
	
	/// @brief Operator == between two hopp::view_ptr<T> (check address, not values)
	/// @param[in] a A hopp::view_ptr<T>
	/// @param[in] b A hopp::view_ptr<T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::view_ptr
	template <class T>
	bool operator ==(hopp::view_ptr<T> const & a, hopp::view_ptr<T> const & b)
	{
		return &a.get() == &b.get();
	}
	
	/// @brief Operator != between two hopp::view_ptr<T> (check address, not values)
	/// @param[in] a A hopp::view_ptr<T>
	/// @param[in] b A hopp::view_ptr<T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::view_ptr
	template <class T>
	bool operator !=(hopp::view_ptr<T> const & a, hopp::view_ptr<T> const & b)
	{
		return (a == b) == false;
	}
	
	/// @brief Operator == between a hopp::view_ptr<T> and a std::nullptr_t
	/// @param[in] a A hopp::view_ptr<T>
	/// @param[in] b A std::nullptr_t
	/// @return true if a is nullptr, false otherwise
	/// @relates hopp::view_ptr
	template <class T>
	bool operator ==(hopp::view_ptr<T> const & a, std::nullptr_t const b)
	{
		hopp_unused(b);
		return bool(a) == false;
	}
	
	/// @brief Operator != between a hopp::view_ptr<T> and a std::nullptr_t
	/// @param[in] a A hopp::view_ptr<T>
	/// @param[in] b A std::nullptr_t
	/// @return true if a is not nullptr, false otherwise
	/// @relates hopp::view_ptr
	template <class T>
	bool operator !=(hopp::view_ptr<T> const & a, std::nullptr_t const b)
	{
		return (a == b) == false;
	}
	
	/// @brief Operator == between a std::nullptr_t and a hopp::view_ptr<T>
	/// @param[in] a A std::nullptr_t
	/// @param[in] b A hopp::view_ptr<T>
	/// @return true if b is nullptr, false otherwise
	/// @relates hopp::view_ptr
	template <class T>
	bool operator ==(std::nullptr_t const a, hopp::view_ptr<T> const & b)
	{
		hopp_unused(a);
		return bool(b) == false;
	}
	
	/// @brief Operator != between a std::nullptr_t and a hopp::view_ptr<T>
	/// @param[in] a A std::nullptr_t
	/// @param[in] b A hopp::view_ptr<T>
	/// @return true if b is not nullptr, false otherwise
	/// @relates hopp::view_ptr
	template <class T>
	bool operator !=(std::nullptr_t const a, hopp::view_ptr<T> const & b)
	{
		return (a == b) == false;
	}
}

#endif
