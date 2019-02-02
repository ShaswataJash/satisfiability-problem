# satisfiability-problem
Boolean satisfiability problem (SAT), maximum satisfiability problem (MAX-SAT) etc

This project is meant for academic purpose. Thus, please do not expect the code to be performant as other SAT solvers developed to win competitions. Main intention for this project is to showcase readable code for understanding some of the important algorithms used in SAT solving domain. Readers can observe that each source file has dedicated comments section to explain the choice of data-structure, code-flow etc.

- **DPLLCppSingleFileUsingSTL.cpp** : Implementation of [DPLL](https://en.wikipedia.org/wiki/DPLL_algorithm) Algorithm with additional enhancement of look-Ahead-Unit-Propagate option and removal of singular polarity variable as an intermediate step. Input formula is accepted in CNF (Conjunctive Normal form) and is represented through DIMACS format.
