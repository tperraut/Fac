// Copyright © 2015 Université Paris-Sud, Written by Lénaïc Bagnères, lenaic.bagneres@u-psud.fr

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

#include <iostream>
#include <fstream>
#include <vector>
#include <list>
#include <algorithm>

#include "hopp/time/now.hpp"
#include "hopp/random.hpp"
#include "hopp/print/std.hpp"
#include <stdlib.h>

template <class T>
void sort(std::vector<T> & v) { std::sort(v.begin(), v.end()); }

template <class T>
void sort(std::list<T> & l) { l.sort(); }


template <class T, class fct_t>
void remove_if(std::vector<T> & v, fct_t const & fct)
{
	v.erase
	(
		std::remove_if(v.begin(), v.end(), fct),
		v.end()
	);
}

template <class T, class fct_t>
void remove_if(std::list<T> & l, fct_t const & fct)
{
	//l.remove_if(fct);
	
	l.erase
	(
		std::remove_if(l.begin(), l.end(), fct),
		l.end()
	);
}


template <class container_t>
void add_and_remove_and_sort(size_t N)
{
	//size_t const N = 10 * 1000 * 1000;
	
	std::cout << "N = " << N << std::endl;
	
	using T = typename container_t::value_type;
	
	container_t c;
	
	// Add
	
	auto const time_add_begin = hopp::now::seconds();
	
	for (size_t i = 0; i < N; ++i)
	{
		/*if (i == 0) {
			c.push_back(-2);
		} else {*/
		c.push_back(T(i % 10) + T(i % 9) / 10.0 + 0.1);
		//}
	}
	
	auto const time_add_end = hopp::now::seconds();
	
	std::cout << "Computation time for add    = " << time_add_end - time_add_begin << " seconds" << std::endl;
	
	// Remove
	
	auto const time_remove_begin = hopp::now::seconds();
	
	c.erase(c.begin());
	//remove_if(c, [](T const & e) { return int(e) == -2 ;});//int(e) == 0;});//int(e) % 3 == 0; });
	
	auto const time_remove_end = hopp::now::seconds();
	
	std::cout << "Computation time for remove = " << time_remove_end - time_remove_begin << " seconds" << std::endl;
	
	// Sort
	
	auto const time_sort_begin = hopp::now::seconds();
	
	sort(c);
	
	auto const time_sort_end = hopp::now::seconds();
	
	std::cout << "Computation time for sort   = " << time_sort_end - time_sort_begin << " seconds" << std::endl;
}


int main(int /*ac*/, char **av)
{
	std::cout << "std::vector<int>" << std::endl;
	add_and_remove_and_sort<std::vector<double>>(size_t(atoi(av[1])));
	std::cout << std::endl;
	
	std::cout << "std::list<int>" << std::endl;
	add_and_remove_and_sort<std::list<double>>(size_t(atoi(av[1])));
	std::cout << std::endl;
	
	return 0;
}
