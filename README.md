# CS202 Assignment 2 : SAT Solver
Team members:
1. L Gokulnath
2. Harsh Trivedi

[Detailed Report](CS202_assignment_2_report.pdf)

## Command to run the SAT Solver
#### For Windows
```
g++ -std=c++11 sat_solver.cpp -o sat_solver
.\sat_solver
```

#### For Linux/Mac
```
g++ -std=c++11 sat_solver.cpp
./a.out
```

## Input
The input is formula in the DIMACS representation. All the formulas are in the testcases folder.

## Output
The solver  
1) returns a model if the formula is satisfiable

2) report that the formula is unsatisfiable

3) also displays the time taken (in seconds) for the execution of the code.

## Limitations
1) The solver is not very efficient in solving formulas having a large number of clauses/variables (of the range > 200)
2) If the formula is SAT, the solver returns only 1 model, it cannot find the number of models nor can it find all the models.




