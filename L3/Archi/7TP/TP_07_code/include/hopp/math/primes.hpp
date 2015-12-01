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


#ifndef HOPP_MATH_PRIMES_HPP
#define HOPP_MATH_PRIMES_HPP

#include <vector>
#include <limits>
#include <cmath>


namespace hopp
{
	namespace math
	{
		/**
		 * @brief Generate prime numbers up to a specified integer
		 *
		 * @b From http://en.wikipedia.org/wiki/Prime_number: @n
		 * A prime number (or a prime) is a natural number greater than 1 that has no positive divisors other than 1 and itself. A natural number greater than 1 that is not a prime number is called a composite number.
		 *
		 * http://en.wikipedia.org/wiki/Sieve_of_Eratosthenes
		 *
		 * @param[in] n Finding all prime numbers up to this integer
		 *
		 * @pre n is an integer
		 * @pre n is positive
		 * @pre n can be transformed into size_t
		 *
		 * @return the all prime numbers up to the parameter n
		 *
		 * @ingroup hopp_math
		 */
		template <class T>
		std::vector<T> primes(T const & n)
		{
			static_assert(std::numeric_limits<T>::is_integer, "hopp::math::primes takes an integer");
			
			std::vector<T> r;
			
			if (n <= 1) { return r; }
			
			std::vector<bool> sieve(size_t(n) + 1, true);
			sieve[0] = false;
			sieve[1] = false;
			
			{
				T i;
				
				for (i = 2; i * i <= n; ++i)
				{
					if (sieve[size_t(i)] == true)
					{
						r.push_back(i);
						
						for (T j = i * i; j <= n; j += i)
						{
							sieve[size_t(j)] = false;
						}
					}
				}
				
				for ( ; size_t(i) < sieve.size(); ++i)
				{
					if (sieve[size_t(i)] == true)
					{
						r.push_back(i);
					}
				}
			}
			
			return r;
		}
	}
}

#endif
