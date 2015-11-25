// Copyright © 2014,  Lénaïc Bagnères, hnc@singularity.fr

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


#ifndef HOPP_RANDOM_HPP
#define HOPP_RANDOM_HPP

/**
 * @defgroup hopp_random Random
 * @copydoc hopp::random
 */

#include <random>
#include <chrono>

#include "time/now.hpp"
#include "int/ulint.hpp"


namespace hopp
{
	/**
	 * @brief Random classes and functions
	 *
	   @code
	   	#include <hopp/random.hpp>
	   @endcode
	 *
	 * @b Example: Quick pseudo random T
	   @code
	   // Pseudo random int
	   hopp::random::uniform(-73, 42); // between -73 and 42
	   hopp::random::uniform(100, 200); // between 100 and 200
	   
	   // Pseudo random unsigned int
	   hopp::random::uniform(42u, 73u);
	   hopp::random::uniform(100u, 200u);
	   
	   // Pseudo random float
	   hopp::random::uniform(0.f, 1.f);
	   hopp::random::uniform(-1.f, 0.f);
	   
	   // Pseudo random double
	   hopp::random::uniform(0.0, 1.0);
	   hopp::random::uniform(-1.0, 0.0);
	   
	   // Pseudo random bool
	   hopp::random::true_false(0.5);
	   hopp::random::true_false();
	   @endcode
	 *
	 * @b Example: Pseudo random T (arithmetic) generator
	   @code
	   // Pseudo random int
	   auto random = hopp::random::make_uniform_t(-73, 42);
	   random(); // between -73 and 42
	   random(100, 200); // between 100 and 200
	   random(); // between -73 and 42
	   @endcode
	 *
	 * @b Example: Pseudo random bool generator
	   @code
	   // Pseudo random bool
	   auto random = hopp::random::make_true_false_t(); // Default probability is 0.5
	   random(); // probability is 0.5
	   random(0.1); // probability is 0.1
	   @endcode
	 */
	namespace random
	{
		// Uniform distributions
		
		// uniform_distribution_t is a type traits to know the std uniform distribution type
		template <class T>
		struct uniform_distribution_t;
		
		// int
		
		// Specialization for int
		template <>
		struct uniform_distribution_t<int>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<int>;
		};
		
		// Specialization for unsigned int
		template <>
		struct uniform_distribution_t<unsigned int>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<unsigned int>;
		};
		
		// Specialization for short int
		template <>
		struct uniform_distribution_t<short int>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<short int>;
		};
		
		// Specialization for unsigned short int
		template <>
		struct uniform_distribution_t<unsigned short int>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<unsigned short int>;
		};
		
		// Specialization for long int
		template <>
		struct uniform_distribution_t<long int>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<long int>;
		};
		
		// Specialization for unsigned long int
		template <>
		struct uniform_distribution_t<unsigned long int>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<unsigned long int>;
		};
		
		// Specialization for long long int
		template <>
		struct uniform_distribution_t<long long int>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<long long int>;
		};
		
		// Specialization for unsigned long long int
		template <>
		struct uniform_distribution_t<unsigned long long int>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<unsigned long long int>;
		};
		
		// Specialization for char
		template <>
		struct uniform_distribution_t<char>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<char>;
		};
		
		// Specialization for unsigned char
		template <>
		struct uniform_distribution_t<unsigned char>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<unsigned char>;
		};
		
		// Specialization for signed char
		template <>
		struct uniform_distribution_t<signed char>
		{
			// Int uniform distribution type
			using type = std::uniform_int_distribution<signed char>;
		};
		
		// double
		
		// Specialization for float
		template <>
		struct uniform_distribution_t<float>
		{
			// Real uniform distribution type
			using type = std::uniform_real_distribution<float>;
		};
		
		// Specialization for double
		template <>
		struct uniform_distribution_t<double>
		{
			// Real uniform distribution type
			using type = std::uniform_real_distribution<double>;
		};
		
		// Specialization for long double
		template <>
		struct uniform_distribution_t<long double>
		{
			// Real uniform distribution type
			using type = std::uniform_real_distribution<long double>;
		};
		
		// bool
		
		// Specialization for bool
		template <>
		struct uniform_distribution_t<bool>
		{
			// Real uniform distribution type
			using type = std::bernoulli_distribution;
		};
		
		
		// Types
		
		/// @brief Pseudo random value with uniform distribution
		/// @ingroup hopp_random
		template <class T>
		class uniform_t
		{
		private:
			
			/// Random engine
			std::default_random_engine m_random_engine;
			
			/// Uniform distribution
			typename hopp::random::uniform_distribution_t<T>::type m_distribution;
			
		public:
			
			/// @brief Constructor
			/// @param[in] min   Minimum value
			/// @param[in] max   Maximum value
			/// @param[in] seed Seed (hopp::now::nanoseconds() by default)
			uniform_t(T const min, T const max, hopp::ulint const seed = hopp::now::nanoseconds<hopp::ulint>()) :
				m_random_engine(seed),
				m_distribution(min, max)
			{ }
			
			/// @brief Default constructor
			uniform_t() : uniform_t(T(0), T(0)) { }
			
			/// @brief Pseudo random value
			/// @return a pseudo random value
			T operator()()
			{
				return m_distribution(m_random_engine);
			}
			
			/// @brief Pseudo random value
			/// @param[in] min Minimum value
			/// @param[in] max Maximum value
			/// @return a pseudo random value between min and max
			T operator()(T const min, T const max)
			{
				typename hopp::random::uniform_distribution_t<T>::type distribution(min, max);
				return distribution(m_random_engine);
			}
		};
		
		/// @brief Pseudo random value with uniform distribution (specialization for bool)
		/// @ingroup hopp_random
		template <>
		class uniform_t<bool>
		{
		private:
			
			/// Random engine
			std::default_random_engine m_random_engine;
			
			/// Uniform distribution
			typename hopp::random::uniform_distribution_t<bool>::type m_distribution;
			
		public:
			
			/// @brief Constructor
			/// @param[in] probability Probability of getting true
			/// @param[in] seed        Seed (hopp::now::nanoseconds() by default)
			uniform_t(double const probability, hopp::ulint const seed = hopp::now::nanoseconds<hopp::ulint>()) :
				m_random_engine(seed),
				m_distribution(probability)
			{ }
			
			/// @brief Default constructor
			uniform_t() : uniform_t(0.5) { }
			
			/// @brief Pseudo random value
			/// @return a pseudo random value
			bool operator()()
			{
				return m_distribution(m_random_engine);
			}
			
			/// @brief Pseudo random value
			/// @param[in] probability Probability of getting true
			/// @return a pseudo random value
			bool operator()(double const probability)
			{
				typename hopp::random::uniform_distribution_t<bool>::type distribution(probability);
				return distribution(m_random_engine);
			}
		};
		
		
		// Make
		
		/// @brief Make a pseudo random uniform object
		/// @param[in] min  Minimum value
		/// @param[in] max  Maximum value
		/// @param[in] seed Seed (hopp::now::nanoseconds() by default)
		/// @return the hopp::random::uniform_t<T> wanted
		/// @ingroup hopp_random
		template <class T>
		hopp::random::uniform_t<T> make_uniform_t(T const min, T const max, hopp::ulint const seed = hopp::now::nanoseconds<hopp::ulint>())
		{
			return hopp::random::uniform_t<T>(min, max, seed);
		}
		
		/// @brief Make a pseudo random uniform object
		/// @param[in] seed Seed (hopp::now::nanoseconds() by default)
		/// @return the hopp::random::uniform_t<T> wanted
		/// @ingroup hopp_random
		template <class T>
		hopp::random::uniform_t<T> make_uniform_t(hopp::ulint const seed = hopp::now::nanoseconds<hopp::ulint>())
		{
			return hopp::random::uniform_t<T>(T(0), T(0), seed);
		}
		
		/// @brief Make a pseudo random uniform object for bool
		/// @param[in] probability Probability of getting true
		/// @param[in] seed        Seed (hopp::now::nanoseconds() by default)
		/// @return the hopp::random::uniform_t<bool> wanted
		/// @ingroup hopp_random
		inline
		hopp::random::uniform_t<bool> make_true_false_t(double const probability, hopp::ulint seed = hopp::now::nanoseconds<hopp::ulint>())
		{
			return hopp::random::uniform_t<bool>(probability, seed);
		}
		
		/// @brief Make a pseudo random uniform object for bool
		/// @param[in] seed Seed (hopp::now::nanoseconds() by default)
		/// @return the hopp::random::uniform_t<bool> wanted
		/// @ingroup hopp_random
		inline
		hopp::random::uniform_t<bool> make_true_false_t(hopp::ulint seed = hopp::now::nanoseconds<hopp::ulint>())
		{
			return hopp::random::uniform_t<bool>(0.5, seed);
		}
		
		
		// Free functions
		
		/// @brief Pseudo random value with uniform distribution
		/// @param[in] min Minimum value
		/// @param[in] max Maximum value
		/// @return the pseudo random value between min and max
		/// @ingroup hopp_random
		template <class T>
		T uniform(T const min, T const max)
		{
			static hopp::random::uniform_t<T> random;
			return random(min, max);
		}
		
		/// @brief Pseudo random bool with uniform distribution
		/// @param[in] probability Probability of getting true
		/// @return true or false
		/// @ingroup hopp_random
		inline
		bool true_false(double const probability = 0.5)
		{
			static hopp::random::uniform_t<bool> random;
			return random(probability);
		}
	}
}

#endif
