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


#ifndef HOPP_CONTAINER_VECTOR2D_HPP
#define HOPP_CONTAINER_VECTOR2D_HPP

#include <iostream>
#include <vector>
#include <stdexcept>
#include <functional>

#include "index.hpp"
#include "vector_view.hpp"
#include "vector2.hpp"


namespace hopp
{
	/**
	 * @brief 2D container
	 *
	 * @code
	   #include <hopp/container/vector2D.hpp>
	   @endcode
	 *
	 * @ingroup hopp_container
	 */
	template <class T>
	class vector2D
	{
	public:
		
		/// Row type
		using row_t = hopp::vector_view<std::vector<T>>;
		
		/// Rows type
		using rows_t = std::vector<row_t>;
		
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
		
	public:
		
		/// Print inline
		bool print_inline;
		
	private:
		
		/// Number of rows
		size_t m_nb_row;
		
		/// Number of columns
		size_t m_nb_col;
		
		/// Vector
		std::vector<T> m_vector;
		
		/// Rows
		rows_t m_rows;
		
	public:
		
		/// @brief Default constructor
		vector2D() :
			print_inline(false),
			m_nb_row(0),
			m_nb_col(0),
			m_vector(),
			m_rows()
		{ }
		
		/// @brief Constructor
		/// @param[in] nb_row        Number of rows
		/// @param[in] nb_col        Number of columns
		/// @param[in] default_value Default value (T() by default)
		vector2D
		(
			size_t const nb_row, size_t const nb_col,
			T const & default_value = T()
		) :
			print_inline(false),
			m_nb_row(nb_row),
			m_nb_col(nb_col),
			m_vector(m_nb_row * m_nb_col, default_value),
			m_rows(m_nb_row)
		{
			update_rows();
		}
		
		/// @brief Constructor from std::vector<std::vector<T>>
		/// @param[in] values A std::vector<std::vector<T>>
		vector2D(std::vector<std::vector<T>> const & values) :
			vector2D(values.size(), values.empty() ? 0 : values[0].size())
		{
			for (size_t i = 0; i < nb_row(); ++i)
			{
				for (size_t j = 0; j < nb_col(); ++j)
				{
					(*this)(i, j) = values[i][j];
				}
			}
		}
		
		/// @brief Copy constructor
		/// @param[in] vector2D A hopp::vector2D<T>
		vector2D(hopp::vector2D<T> const & vector2D) :
			print_inline(vector2D.print_inline),
			m_nb_row(vector2D.nb_row()),
			m_nb_col(vector2D.nb_row()),
			m_vector(vector2D.vector()),
			m_rows()
		{
			update_rows();
		}
		
		/// @brief Move constructor
		/// @param[in] vector2D A hopp::vector2D<T>
		vector2D(hopp::vector2D<T> && vector2D) :
			print_inline(vector2D.print_inline),
			m_nb_row(vector2D.nb_row()),
			m_nb_col(vector2D.nb_row()),
			m_vector(std::move(vector2D.m_vector)),
			m_rows()
		{
			update_rows();
		}
		
		/// @brief Assignment operator
		/// @param[in] vector2D A hopp::vector2D<T>
		/// @return the vector2D
		hopp::vector2D<T> const & operator =(hopp::vector2D<T> const & vector2D)
		{
			hopp::vector2D<T> tmp = vector2D;
			swap(*this, tmp);
			return *this;
		}
		
		/// @brief Move assignment operator
		/// @param[in] vector2D A hopp::vector2D<T>
		/// @return the vector2D
		hopp::vector2D<T> const & operator =(hopp::vector2D<T> && vector2D)
		{
			swap(*this, vector2D);
			return *this;
		}
		
		/// @brief Swap two hopp::vector2D<T>
		/// @param[in] a A hopp::vector2D<T>
		/// @param[in] b A hopp::vector2D<T>
		friend void swap(hopp::vector2D<T> & a, hopp::vector2D<T> & b) noexcept
		{
			std::swap(a.print_inline, b.print_inline);
			std::swap(a.m_nb_row, b.m_nb_row);
			std::swap(a.m_nb_col, b.m_nb_col);
			std::swap(a.m_vector, b.m_vector);
			std::swap(a.m_rows, b.m_rows);
			a.update_rows();
			b.update_rows();
		}
		
		// Size, Vector & Data
		
		/// @brief Return the number of rows
		/// @return the number of rows
		size_t nb_row() const { return m_nb_row; }
		
		/// @brief Return the number of rows
		/// @return the number of rows
		size_t size() const { return nb_row(); }
		
		/// @brief Return the number of columns
		/// @return the number of columns
		size_t nb_col() const { return m_nb_col; }
		
		/// @brief Get vector
		/// @return vector
		std::vector<T> const & vector() const { return m_vector; }
		
		/// @brief Get vector
		/// @return vector
		std::vector<T> & vector() { return m_vector; }
		
		/// @brief Get data
		/// @return data
		const_pointer data() const { return m_vector.data(); }
		
		/// @brief Get data
		/// @return data
		pointer data() { return m_vector.data(); }
		
		// Access: operator (i, j)
		
		/// @brief Const value access
		/// @param i Row index
		/// @param j Column index
		/// @return the value at (i, j)
		T const & operator ()(size_t const i, size_t const j) const
		{
			return m_vector[hopp::index2D::index1D(i, j, nb_col())];
		}
		
		/// @brief Value access
		/// @param i Row index
		/// @param j Column index
		/// @return the value at (i, j)
		T & operator ()(size_t const i, size_t const j)
		{
			return m_vector[hopp::index2D::index1D(i, j, nb_col())];
		}
		
		// Access: .at(i, j)
		
		/// @brief Safe const value access
		/// @param i Row index
		/// @param j Column index
		/// @return the value at (i, j)
		/// @exception std::out_of_range if i >= number of rows or j >= number of columns
		T const & at(size_t const i, size_t const j) const
		{
			if (i >= nb_row()) { throw std::out_of_range("hopp::vector2D<T>:at(i, j): invalid i index"); }
			if (j >= nb_col()) { throw std::out_of_range("hopp::vector2D<T>:at(i, j): invalid j index"); }
			return (*this)(i, j);
		}
		
		/// @brief Value safe access
		/// @param i Row index
		/// @param j Column index
		/// @return the value at (i, j)
		/// @exception std::out_of_range if i >= number of rows or j >= number of columns
		T & at(size_t const i, size_t const j)
		{
			if (i >= nb_row()) { throw std::out_of_range("hopp::vector2D<T>:at(i, j): invalid i index"); }
			if (j >= nb_col()) { throw std::out_of_range("hopp::vector2D<T>:at(i, j): invalid j index"); }
			return (*this)(i, j);
		}
		
		// Access: operator [i]
		
		/// @brief Const row access
		/// @param i Row index
		/// @return row at i
		row_t const & operator [](size_t const i) const { return m_rows[i]; }
		
		/// @brief Line access
		/// @param i Row index
		/// @return row at i
		row_t & operator [](size_t const i) { return m_rows[i]; }
		
		// Access: .at(i)
		
		/// @brief Const safe row access
		/// @param i Row index
		/// @return row at i
		/// @exception std::out_of_range if i >= number of rows
		row_t const & at(size_t const i) const
		{
			if (i >= nb_row()) { throw std::out_of_range("hopp::vector2D<T>:at(i): invalid i index"); }
			return m_rows[i];
		}
		
		/// @brief Safe row access
		/// @param i Row index
		/// @return row at i
		/// @exception std::out_of_range if i >= number of rows
		row_t & at(size_t const i)
		{
			if (i >= nb_row()) { throw std::out_of_range("hopp::vector2D<T>:at(i): invalid i index"); }
			return m_rows[i];
		}
		
		// front, back
		
		/// @brief Get first row
		/// @pre Number of rows is not zero
		/// @return first row
		row_t const & front() const { return m_rows.front(); }
		
		/// @brief Get first row
		/// @pre Number of rows is not zero
		/// @return first row
		row_t & front() { return m_rows.front(); }
		
		/// @brief Get last row
		/// @pre Number of rows is not zero
		/// @return last row
		row_t const & back() const { return m_rows.back(); }
		
		/// @brief Get last row
		/// @pre Number of rows is not zero
		/// @return last row
		row_t & back() { return m_rows.back(); }
		
		// Iterator
		
		/// @brief Get const iterator to beginning
		/// @return const iterator to beginning
		const_iterator begin() const { return m_rows.begin(); }
		
		/// @brief Get const iterator to beginning
		/// @return const iterator to beginning
		const_iterator cbegin() const { return m_rows.cbegin(); }
		
		/// @brief Get iterator to beginning
		/// @return iterator to beginning
		iterator begin() { return m_rows.begin(); }
		
		/// @brief Get const iterator to end
		/// @return const iterator to end
		const_iterator end() const { return m_rows.end(); }
		
		/// @brief Get const iterator to end
		/// @return const iterator to end
		const_iterator cend() const { return m_rows.cend(); }
		
		/// @brief Get iterator to end
		/// @return iterator to end
		iterator end() { return m_rows.end(); }
		
		// Reverse iterator
		
		/// @brief Get const reverse iterator to reverse beginning
		/// @return const reverse iterator to reverse beginning
		const_reverse_iterator rbegin() const { return m_rows.rbegin(); }
		
		/// @brief Get const reverse iterator to reverse beginning
		/// @return const reverse iterator to reverse beginning
		const_reverse_iterator crbegin() const { return m_rows.crbegin(); }
		
		/// @brief Get reverse iterator to reverse beginning
		/// @return reverse iterator to reverse beginning
		reverse_iterator bregin() { return m_rows.rbegin(); }
		
		/// @brief Get const reverse iterator to reverse end
		/// @return const reverse iterator to reverse end
		const_reverse_iterator rend() const { return m_rows.rend(); }
		
		/// @brief Get const reverse iterator to reverse end
		/// @return const reverse iterator to reverse end
		const_reverse_iterator crend() const { return m_rows.crend(); }
		
		/// @brief Get reverse iterator to reverse end
		/// @return reverse iterator to reverse end
		reverse_iterator rend() { return m_rows.rend(); }
		
		// Add
		
		/// @brief Add a row before an index
		/// @param[in] i             Row index
		/// @param[in] default_value Default value (T() by default)
		/// @exception std::out_of_range if NDEBUG is not defined and if i > number of rows
		void add_row_before(size_t const i, T const & default_value = T())
		{
			#ifndef NDEBUG
				if (i > nb_row()) { throw std::out_of_range("hopp::vector2D<T>:add_row_before(i): invalid i index"); }
			#endif
			
			hopp::vector2D<T> tmp(nb_row() + 1, nb_col());
			
			// Copy rows before new row
			for (size_t row = 0; row < i; ++row)
			{
				for (size_t col = 0; col < nb_col(); ++col)
				{ tmp(row, col) = (*this)(row, col); }
			}
			// Insert line
			for (size_t col = 0; col < tmp.nb_col(); ++col)
			{
				tmp(i, col) = default_value;
			}
			// Copy rows after new row
			for (size_t row = i; row < nb_row(); ++row)
			{
				for (size_t col = 0; col < nb_col(); ++col)
				{ tmp(row + 1, col) = (*this)(row, col); }
			}
			
			*this = std::move(tmp);
		}
		
		/// @brief Add a row after an index
		/// @param[in] i             Row index
		/// @param[in] default_value Default value (T() by default)
		/// @exception std::out_of_range if NDEBUG is not defined and if i + 1 > number of rows
		void add_row_after(size_t const i, T const & default_value = T())
		{
			add_row_before(i + 1, default_value);
		}
		
		/// @brief Add a column before an index
		/// @param[in] j             Column index
		/// @param[in] default_value Default value (T() by default)
		/// @exception std::out_of_range if NDEBUG is not defined and if j > number of columns
		void add_col_before(size_t const j, T const & default_value = T())
		{
			#ifndef NDEBUG
				if (j > nb_col()) { throw std::out_of_range("hopp::vector2D<T>:add_col_before(j): invalid j index"); }
			#endif
			
			hopp::vector2D<T> tmp(nb_row(), nb_col() + 1);
			
			// Copy rows before new row
			for (size_t row = 0; row < nb_row(); ++row)
			{
				// Copy all col before new col
				for (size_t col = 0; col < j; ++col)
				{
					tmp(row, col) = (*this)(row, col);
				}
				// Insert value
				tmp(row, j) = default_value;
				// Copy all col after new col
				for (size_t col = j; col < nb_col(); ++col)
				{
					tmp(row, col + 1) = (*this)(row, col);
				}
			}
			
			*this = std::move(tmp);
		}
		
		/// @brief Add a column after an index
		/// @param[in] j             Column index
		/// @param[in] default_value Default value (T() by default)
		/// @exception std::out_of_range if NDEBUG is not defined and if j + 1 > number of columns
		void add_col_after(size_t const j, T const & default_value = T())
		{
			add_col_before(j + 1, default_value);
		}
		
		// Remove
		
		/// @brief Remove a row
		/// @param[in] i Row index
		/// @exception std::out_of_range if NDEBUG is not defined and if i >= number of rows
		void remove_row(size_t const i)
		{
			#ifndef NDEBUG
			if (i >= nb_row()) { throw std::out_of_range("hopp::vector2D<T>:remove_row(i): invalid i index"); }
			#endif
			
			hopp::vector2D<T> tmp(nb_row() - 1, nb_col());
			
			// Copy rows before i
			for (size_t row = 0; row < i; ++row)
			{
				for (size_t col = 0; col < nb_col(); ++col)
				{ tmp(row, col) = (*this)(row, col); }
			}
			// Copy rows after i
			for (size_t row = i + 1; row < nb_row(); ++row)
			{
				for (size_t col = 0; col < nb_col(); ++col)
				{ tmp(row - 1, col) = (*this)(row, col); }
			}
			
			*this = std::move(tmp);
		}
		
		/// @brief Remove a column
		/// @param[in] j Column index
		/// @exception std::out_of_range if NDEBUG is not defined and if j >= number of columns
		void remove_col(size_t const j)
		{
			#ifndef NDEBUG
			if (j >= nb_col()) { throw std::out_of_range("hopp::vector2D<T>:remove_col(j): invalid j index"); }
			#endif
			
			hopp::vector2D<T> tmp(nb_row(), nb_col() - 1);
			
			// Copy rows
			for (size_t row = 0; row < nb_row(); ++row)
			{
				// Copy columns bejore j
				for (size_t col = 0; col < j; ++col)
				{
					tmp(row, col) = (*this)(row, col);
				}
				// Copy columns after j
				for (size_t col = j + 1; col < nb_col(); ++col)
				{
					tmp(row, col - 1) = (*this)(row, col);
				}
			}
			
			*this = std::move(tmp);
		}
		
	private:
		
		/// @brief Update rows
		void update_rows()
		{
			m_rows.resize(nb_row());
			
			for (size_t i = 0; i < nb_row(); ++i)
			{
				m_rows[i] = hopp::make_vector_view
				            (
				            	vector(),
				            	hopp::index2D::index1D(i, size_t(0), nb_col()),
				            	hopp::index2D::index1D(i, nb_col(), nb_col())
				            );
			}
		}
	};
	
	/// @brief Operator << between a std::ostream and a hopp::vector2D<T>
	/// @param[in,out] out      A std::ostream
	/// @param[in]     vector2D A hopp::vector2D<T>
	/// @return out
	/// @relates hopp::vector2D
	template <class T>
	std::ostream & operator <<(std::ostream & out, hopp::vector2D<T> const & vector2D)
	{
		if (vector2D.nb_row() == 0)
		{
			out << "{ }";
		}
		else if (vector2D.print_inline)
		{
			out << "{";
			for (size_t row = 0; row < vector2D.nb_row(); ++row)
			{
				if (row == 0) { out << " "; }
				else { out << ", "; }
				
				out << "{ ";
				for (size_t col = 0; col < vector2D.nb_col(); ++col)
				{
					if (col != 0) { out << ", "; }
					out << vector2D(row, col);
				}
				out << " }";
			}
			out << " }";
		}
		else
		{
			out << "{\n";
			for (size_t row = 0; row < vector2D.nb_row(); ++row)
			{
				out << "\t{ ";
				for (size_t col = 0; col < vector2D.nb_col(); ++col)
				{
					if (col != 0) { out << ", "; }
					out << vector2D(row, col);
				}
				out << " }";
				
				if (row != vector2D.nb_row() - 1) { out << ",\n"; }
			}
			out << "\n}";
		}

		return out;
	}
	
	/// @brief Operator == between two hopp::vector2D<T>
	/// @param[in] a A hopp::vector2D<T>
	/// @param[in] b A hopp::vector2D<T>
	/// @return true if a == b, false otherwise
	/// @relates hopp::vector2D
	template <class T>
	bool operator ==(hopp::vector2D<T> const & a, hopp::vector2D<T> const & b)
	{
		return a.nb_row() == b.nb_row() && a.nb_col() == b.nb_col() && a.vector() == b.vector();
	}
	
	/// @brief Operator != between two hopp::vector2D<T>
	/// @param[in] a A hopp::vector2D<T>
	/// @param[in] b A hopp::vector2D<T>
	/// @return true if a != b, false otherwise
	/// @relates hopp::vector2D
	template <class T>
	bool operator !=(hopp::vector2D<T> const & a, hopp::vector2D<T> const & b)
	{
		return (a == b) == false;
	}
}

#endif
