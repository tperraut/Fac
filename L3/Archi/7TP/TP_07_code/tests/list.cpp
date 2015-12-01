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
#include <list>
#include <algorithm>

#include "hopp/time/now.hpp"
#include "hopp/random.hpp"
#include "hopp/print/std.hpp"
#include <stdlib.h>

int main(int /*argc*/, char * * argv)
{
	size_t const N = size_t(atoi(argv[1]));
	
	std::cout << argv[0] << " (N = " << N << ")" << std::endl;
	
	std::list<double> l(N);
	
	{
		size_t i = 0;
		for (auto it = l.begin(); it != l.end(); ++it)
		{
			//auto const i = std::distance(it, l.begin());
			*it = double(i % 10) + double(i % 9) / 10.0 + 0.1;
			++i;
		}
	}
	
	// Sum
	
	auto const time_sum_begin = hopp::now::seconds();
	
	double sum = 0.0;
	
	for (auto it = l.begin(); it != l.end(); ++it)
		{
			sum += *it;
		}
	
	auto const time_sum_end = hopp::now::seconds();
	
	// Sum ref
	
	auto const time_sum_ref_begin = hopp::now::seconds();
	
	auto const sum_ref = std::accumulate(l.begin(), l.end(), 0.0);
	
	auto const time_sum_ref_end = hopp::now::seconds();
	
	// Sum display
	
	std::cout << "Sum = " << sum << std::endl;
	if (sum != sum_ref)
	//if (std::abs((sum_ref - sum) / sum_ref) >= 0.01 / 100.0)
	{ std::cout << "Error: " << sum << " != " << sum_ref << std::endl; }
	
	std::cout << "Computation time for sum     = " << time_sum_end - time_sum_begin << " seconds" << std::endl;
	std::cout << "Computation time for sum_ref = " << time_sum_ref_end - time_sum_ref_begin << " seconds" << std::endl;
	std::cout << std::endl;
	
	// Mean (same as expected value)
	double mean = sum / double(l.size());
	
	// Variance
	
	auto const time_variance_begin = hopp::now::seconds();
	
	double variance = 0.0;
	
	for (auto it = l.begin(); it != l.end(); ++it)
		{
			variance += (*it - mean)*(*it-mean);
		}
	
	auto const time_variance_end = hopp::now::seconds();
	
	// Variance ref
	
	auto const time_variance_ref_begin = hopp::now::seconds();
	
	auto const variance_ref =
		std::accumulate
		(
			l.begin(), l.end(), 0.0,
			[mean](double const variance, double const e)
			{
				auto const tmp = e - mean;
				return variance + tmp * tmp;
			}
		);
	
	auto const time_variance_ref_end = hopp::now::seconds();
	
	std::cout << "Variance = " << variance << std::endl;
	if (variance != variance_ref)
	//if (std::abs((variance_ref - variance) / variance_ref) >= 0.01 / 100.0)
	{ std::cout << "Error: " << variance << " != " << variance_ref << std::endl; }
	
	std::cout << "Computation time for variance     = " << time_variance_end - time_variance_begin << " seconds" << std::endl;
	std::cout << "Computation time for variance_ref = " << time_variance_ref_end - time_variance_ref_begin << " seconds" << std::endl;
	std::cout << std::endl;
	
	// Standard deviation
	double standard_deviation = std::sqrt(variance);
	std::cout << "Standard deviation = " << standard_deviation << std::endl;
	std::cout << std::endl;
	
	return 0;
}
