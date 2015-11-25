// Copyright © 2011, 2012 the Ohio State University, Written by Louis-Noel Pouchet, pouchet@cse.ohio-state.edu
// Copyright © 2014 Inria, Written by Lénaïc Bagnères, lenaic.bagneres@inria.fr
// Copyright © 2015 Lénaïc Bagnères, hnc@singularity.fr

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 2 of the License
// 
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>

#include <iostream>
#include <fstream>
#include <stdlib.h>

#include "hopp/time/now.hpp"
#include "hopp/container/vector2D.hpp"
#include <omp.h>


// Matrix-multiply R = alpha * A * B + beta

int main(int /*argc*/, char * * argv)
{
	bool const display = false;
	bool const write = true;
	size_t x = size_t(atoi(argv[1]));

	size_t const NB_ROW_A = x;
	size_t const NB_COL_A = x;
	size_t const NB_COL_B = x;
	
	std::cout << argv[0] << " (NB_ROW_A = " << NB_ROW_A << ", NB_COL_A = " << NB_COL_A << ", NB_COL_B = " << NB_COL_B << ")" << std::endl;
	
	size_t const NB_ROW_B = NB_COL_A;
	size_t const NB_ROW_R = NB_ROW_A;
	size_t const NB_COL_R = NB_COL_B;
	
	hopp::vector2D<double> A(NB_ROW_A, NB_COL_A);
	hopp::vector2D<double> B(NB_ROW_B, NB_COL_B);
	hopp::vector2D<double> R(NB_ROW_R, NB_COL_R);
	
	double const alpha = 32412;
	double const beta = 2123;
	
	for (size_t i = 0; i < NB_ROW_A; ++i)
	{
		for (size_t j = 0; j < NB_COL_A; ++j)
		{
			A[i][j] = double(i * j) / double(NB_ROW_A);
		}
	}
	
	for (size_t i = 0; i < NB_ROW_B; ++i)
	{
		for (size_t j = 0; j < NB_COL_B; ++j)
		{
			B[i][j] = double(i * j) / double(NB_ROW_A);
		}
	}
	
	auto const begin = hopp::now::seconds();
	// R = alpha * A * B + beta
	//#pragma omp parallel for
	for (size_t i = 0; i < NB_ROW_R; i++)
	{
		for (size_t j = 0; j < NB_COL_R; j++)
			R[i][j] = beta;
		for (size_t k = 0; k < NB_COL_A; ++k) 
		{
			for (size_t j = 0; j < NB_COL_R; j++)
			{
				R[i][j] += alpha * A[i][k] * B[k][j];
			}
		}
	}
	
	auto const end = hopp::now::seconds();
	
	std::cout << "Time = " << end - begin << " seconds" << std::endl;
	std::cout << std::endl;
	
	// Display
	if (display)
	{
		std::cout << "R =" << std::endl;
		std::cout << R << std::endl;
		std::cout << std::endl;
	}
	
	// Write
	if (write)
	{
		std::ofstream log(argv[0] + std::string(".log"));
		
		for (size_t i = 0; i < NB_ROW_R; ++i)
		{
			for (size_t j = 0; j < NB_COL_R; ++j)
			{
				log << R[i][j] << " ";
			}
			log << "\n";
		}
		log << "\n";
	}
	
	return 0;
}
