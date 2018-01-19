// An Interacting Replica approach incorporating Warning Propagation applied to the kSAT Problem

// Blake Leonard 2011

// Physics Department
// Washington University in St. Louis

#include <iostream>
using namespace::std;

#include <fstream>
using namespace::std;

#include <cmath>
using namespace::std; 

#include <ctime>
using namespace::std;


void main ()
{
	const int r = 1;       			// number of replicas

	const int k = 3;       			// variables per clause ( # of variable nodes connected to a given function node )

	const int n = 10;       		// number of variables  ( variable nodes )   ( k <= n <= k * m )

	const int m = 42;     			// number of clauses    ( function nodes )

	const float F = 0.1;        		// Convergence Factor

	int wp_steps = 5;
	int global_steps = 3000;
	int min_unsatisfied_clauses = m;

	int mstep, kstep, k1step, gstep, istep, jstep, lstep, nstep, rstep;
	int contradiction_counter, verification_counter, unsatisfied_counter, unsatisfied_clauses;
	float total_error[r];
	float complete_error;

	int function_node_connections[m][k];
	int warning[r][m][k];

	float average_cavity_field[m][k];

	int c[m][k];
	float cavity_field[r][m][k];
	float old_cavity_field[r][m][k];
	int local_field[r][n];
	int contradiction_number[r][n];
	int variable_value[r][n];

	int best_found_variable_value[n];
	int best_variable_value[n];

	srand(time(0));


	// Construct Factor Graph of random kSAT problem

	for ( mstep = 0; mstep < m; mstep ++ )
	{

		for ( kstep = 0; kstep < k; kstep ++ )
		{

			// Generate random connections from function nodes to variable nodes

			function_node_connections[mstep][kstep] = rand() %  n; 

			for ( lstep = 0; lstep < kstep; lstep ++ )
			{

				while ( function_node_connections[mstep][kstep] == function_node_connections[mstep][lstep] )
				{

					function_node_connections[mstep][kstep] = rand() %  n; 

				}

			}


			// Generate random negations of variables in clauses

			c[mstep][kstep] = rand() % 2;

			if ( c[mstep][kstep] == 0 )
			{
 
				c[mstep][kstep] = -1;

			}

		}

	}

	
	// Print statement of problem

	for ( mstep = 0; mstep < m; mstep ++ )
	{

		cout << "( ";

		for ( kstep = 0; kstep < k; kstep ++ )
		{

			if ( c[mstep][kstep] == ( - 1 ) )
			{
		
				cout << "NOT";
			
			}

			cout << function_node_connections[mstep][kstep];

			if ( kstep != ( k - 1) )
			{

				cout << " OR ";

			}

		}

		cout << " )";


		if ( mstep != ( m - 1 ) )
		{

			cout << " AND ";

		}

	}

	cout << endl << endl;


	// Brute Force Solution
 
	for ( istep = 0; istep < n; istep ++ )
	{
		variable_value[0][istep] = 0;
	}


	for	( istep = 0; istep < pow(2, n); istep ++ )
	{

		// add 1 to binary number

		for ( jstep = n-1; jstep >= 0; jstep -- )
		{

			if ( variable_value[0][jstep] == 0 )
			{
				variable_value[0][jstep] = 1;

				for ( kstep = jstep + 1; kstep < n; kstep ++ )
				{
					variable_value[0][kstep] = 0;
				}

				break;
			}

		}


		// Check new configuration

		unsatisfied_clauses = 0;

		for ( mstep = 0; mstep < m; mstep ++ )
		{

			unsatisfied_counter = 0;

			for ( kstep = 0; kstep < k; kstep ++ )
			{

				if( ( ( c[mstep][kstep] > 0 ) & ( variable_value[0][ function_node_connections[mstep][kstep] ] == 0 ) ) || ( ( c[mstep][kstep] < 0 ) & ( variable_value[0][ function_node_connections[mstep][kstep] ] == 1 ) ) )
				{

					unsatisfied_counter ++; 	

				}

			}

			if ( unsatisfied_counter == k )
			{

				unsatisfied_clauses ++;

			}

		}

		if ( unsatisfied_clauses < min_unsatisfied_clauses )
		{
			min_unsatisfied_clauses = unsatisfied_clauses;

			for ( jstep = 0; jstep < n; jstep ++ )
			{
				best_variable_value[jstep] = variable_value[0][jstep];
			}

		}

	}


	srand(time(0));


	// Generate initial random warnings ( either 0 or 1 ) for all replicas

	for ( rstep = 0; rstep < r; rstep ++ )
	{

		for ( mstep = 0; mstep < m; mstep ++ )
		{

			for ( kstep = 0; kstep < k; kstep ++ )
			{

				warning[rstep][mstep][kstep] = rand() % 2;

			}		

		}

	}


	// Global Steps 

	for ( gstep = 0; gstep < global_steps ; gstep ++ )
	{

		// WP Algorithm ( alternate between updating warnings and cavity fields for each replica)

		for ( istep = 0; istep < wp_steps; istep ++ )
		{

			// Generate Cavity Fields based on warnings

			for ( rstep = 0; rstep < r; rstep ++ )
			{

				total_error[rstep] = 0;

				for ( mstep = 0; mstep < m; mstep ++ )
				{

					for ( kstep = 0; kstep < k; kstep ++ )
					{

						// Cavity Field for an edge is sum of all warnings to particular variable node excluding the particular function node
						// Cavity Field is a message from variable node to function node based on info from other function nodes

						cavity_field[rstep][mstep][kstep] = 0;

						for ( lstep = 0; lstep < m; lstep ++ )
						{
							for ( k1step = 0; k1step < k; k1step ++ )
							{

								if ( ( lstep != mstep ) & ( function_node_connections[lstep][kstep] == function_node_connections[mstep][k1step] ) )
								{

									cavity_field[rstep][mstep][kstep] = cavity_field[rstep][mstep][kstep] + c[lstep][k1step] * warning[rstep][lstep][k1step];

								}

							}

						}


						if ( gstep != 0)
						{
							
							total_error[rstep] = total_error[rstep] + abs ( cavity_field[rstep][mstep][kstep] - old_cavity_field[rstep][mstep][kstep] );

						}

						old_cavity_field[rstep][mstep][kstep] = cavity_field[rstep][mstep][kstep];

					}		

				}

				cout << total_error[rstep] << endl;

			}


			// Compute average value of cavity fields over all replicas

			for ( mstep = 0; mstep < m; mstep ++ )
			{

				for ( kstep = 0; kstep < k; kstep ++ )
				{

					average_cavity_field[mstep][kstep] = 0;

					for ( rstep = 0; rstep < r; rstep ++ )
					{

						average_cavity_field[mstep][kstep] = average_cavity_field[mstep][kstep] + cavity_field[rstep][mstep][kstep];

					}

					average_cavity_field[mstep][kstep] = average_cavity_field[mstep][kstep] / r;
					
				}

			}


			// Check if any replicas have converged and if so apply info coupling method

			for ( rstep = 0; rstep < r; rstep ++ )
			{

				if ( total_error[rstep] == 0 )
				{

					// Alter Cavity Fields based on average values over replicas
				
					for ( mstep = 0; mstep < m; mstep ++ )
					{

						for ( kstep = 0; kstep < k; kstep ++ )
						{

							cout << " cavity_field[" << rstep << "][" << mstep << "][" << kstep << "] changed from " << cavity_field[rstep][mstep][kstep] << " to ";

							cavity_field[rstep][mstep][kstep] = cavity_field[rstep][mstep][kstep] - F * ( cavity_field[rstep][mstep][kstep] - average_cavity_field[mstep][kstep] );

							cout << cavity_field[rstep][mstep][kstep] << endl;

						}

					}

				}

			}
		

			// Generate warnings based on cavity fields
	
			for ( rstep = 0; rstep < r; rstep ++ )
			{

				for ( mstep = 0; mstep < m; mstep ++ )
				{

					for ( kstep = 0; kstep < k; kstep ++ )
					{

						warning[rstep][mstep][kstep] = 1; 

						// Warning along an edge is product of all cavity fields sign for particular function node excluding the particular variable node 
						// Warning is a message from function node to variable node based on info from other variable nodes

						for ( lstep = 0; lstep < k; lstep ++ )
						{
							if ( lstep != kstep )
							{

								if ( (  ( c[mstep][lstep] < 0 ) & ( cavity_field[rstep][mstep][lstep] <= 0 )  ) || (  ( c[mstep][lstep] > 0 ) & ( cavity_field[rstep][mstep][lstep] > 0 )  ) )
								{

									warning[rstep][mstep][kstep] = 0 ;

								}
		
							}

						}

					}		

				}

			}

		}
		

		// Complete error among replicas

		complete_error = 0;

		for ( rstep = 0; rstep < r; rstep ++ )
		{
			
			complete_error = complete_error + total_error[rstep];

		}

		cout << complete_error << " aa " << endl;

		if ( ( gstep != 0 ) & ( complete_error == 0 ) )
		{

			gstep = global_steps;

		}

	}


	// Calculate Local Fields and contradiction numbers based on warnings 
	
	for ( rstep = 0; rstep < r; rstep ++ )
	{

		for ( nstep = 0; nstep < n; nstep ++ )
		{

			local_field[rstep][nstep] = 0;

			contradiction_number[rstep][nstep] = 1;

			contradiction_counter = 0;

			verification_counter = 0;


			// Local field is the sum of all the warnings to a variable node

			for ( mstep = 0; mstep < m; mstep ++ )
			{
			
				for ( kstep = 0; kstep < k; kstep ++ )
				{

					if( function_node_connections[mstep][kstep] == nstep  )
					{

						local_field[rstep][nstep] = local_field[rstep][nstep] + c[mstep][kstep] * warning[rstep][mstep][kstep];

						contradiction_counter = contradiction_counter + warning[rstep][mstep][kstep];

						verification_counter = verification_counter ++ ;
					
					}

				}

			}

			if ( ( contradiction_counter == 0 ) || ( contradiction_counter == verification_counter ) )
			{

				contradiction_number[rstep][nstep] = 0;	

			}

		}

	}


	// Print Brute Force Solution

	cout << endl << "Brute Force Solution: " << endl << endl;

	cout << "   values: " << endl;


	for ( nstep = 0; nstep < n; nstep ++ )
	{	
		cout << nstep << ":	 " << best_variable_value[nstep] << endl;
		
	}

	cout << "Number of Unsatasfied Clauses: " << min_unsatisfied_clauses << endl << endl << endl;


	// Set variable values according to local fields and check if formula is satisfied

	cout << "WP-IR Solution: " << endl << endl;

	cout << "   values:	" << endl;

	min_unsatisfied_clauses = m;


	for ( rstep = 0; rstep < r; rstep ++ )
	{

		for ( nstep = 0; nstep < n; nstep ++ )
		{

			if ( local_field[rstep][nstep] <= 0 )
			{

				variable_value[rstep][nstep] = 0;

			}
			else
			{

				variable_value[rstep][nstep] = 1;

			}

		}


		unsatisfied_clauses = 0;

		for ( mstep = 0; mstep < m; mstep ++ )
		{

			unsatisfied_counter = 0;

			for ( kstep = 0; kstep < k; kstep ++ )
			{

				if( ( ( c[mstep][kstep] > 0 ) & ( variable_value[rstep][ function_node_connections[mstep][kstep] ] == 0 ) ) || ( ( c[mstep][kstep] < 0 ) & ( variable_value[rstep][ function_node_connections[mstep][kstep] ] == 1 ) ) )
				{

					unsatisfied_counter ++; 	

				}

			}

			if ( unsatisfied_counter == k )
			{

				unsatisfied_clauses ++;

			}

		}

		if ( unsatisfied_clauses < min_unsatisfied_clauses )
		{
			min_unsatisfied_clauses = unsatisfied_clauses;

			for ( istep = 0; istep < n; istep ++ )
			{

				best_found_variable_value[istep] = variable_value[rstep][istep];
		
			}	

		}

	}


	// Print best solution found by WP-IR

	for ( nstep = 0; nstep < n; nstep ++ )
	{

		cout << nstep << ":	 " << best_found_variable_value[nstep] << endl;
	
	}

	
	cout << endl << endl << "Number of Unsatisfied Clauses: " << min_unsatisfied_clauses << endl;


	return;
}
