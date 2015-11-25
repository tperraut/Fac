// Copyright © 2015 Inria, Written by Lénaïc Bagnères, lenaic.bagneres@inria.fr

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


#ifndef HOPP_MATH_INTEGER_FACTORIZATION_HPP
#define HOPP_MATH_INTEGER_FACTORIZATION_HPP

#include <vector>
#include <limits>

#include "primes.hpp"


namespace hopp
{
	namespace math
	{
		/**
		 * @brief Integer factorization
		 *
		 * @b From http://en.wikipedia.org/wiki/Integer_factorization: @n
		 * In number theory, integer factorization is the decomposition of a composite number into a product of smaller integers. If these integers are further restricted to prime numbers, the process is called prime factorization.
		 *
		 * @param[in] i An integer
		 *
		 * @pre i is an integer
		 *
		 * @return the decomposition
		 *
		 * @ingroup hopp_math
		 */
		template <class T>
		std::vector<T> integer_factorization(T const & i)
		{
			static_assert(std::numeric_limits<T>::is_integer, "hopp::math::integer_factorization works only on integer");
			
			if (i < T(0))
			{
				auto r = hopp::math::integer_factorization(-i);
				r.push_back(T(-1));
				return r;
			}
			
			if (i <= T(3))
			{
				return std::vector<T>({ i });
			}
			
			std::vector<T> r;
			
			T tmp = i;
			
			std::vector<T> primes = hopp::math::primes(i);
			
			for (auto prime_it = primes.crbegin(); prime_it != primes.crend(); ++prime_it)
			{
				while (tmp % *prime_it == 0)
				{
					tmp /= *prime_it;
					r.push_back(*prime_it);
				}
			}
			
			return r;
		}
	}
}

#endif
