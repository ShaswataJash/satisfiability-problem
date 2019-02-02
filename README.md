# satisfiability-problem
Boolean satisfiability problem (SAT), maximum satisfiability problem (MAX-SAT) etc

This project is meant for academic purpose. Thus, please do not expect the code to be performant as other SAT solvers developed to win competitions. Main intention for this project is to showcase readable code for understanding some of the important algorithms used in SAT solving domain. Readers can observe that each source file has dedicated comments section to explain the choice of data-structure, code-flow etc. Intentionally, each of teh source file is kept self sufficient i.e. in each of the file itself you will find code for algorithm, DIMACS format file parsing and main() function.

```To compile any of the source file:  g++ -o <executable name> -O2 --std=c++11 <source-file-name>.cpp ```

- **DPLLCppSingleFileUsingSTL.cpp** : Implementation of [DPLL](https://en.wikipedia.org/wiki/DPLL_algorithm) Algorithm with additional enhancement of look-Ahead-Unit-Propagate option and removal of singular polarity variable as an intermediate step. Input formula is accepted in CNF (Conjunctive Normal form) and is represented through DIMACS format.

### Benchmark experiments
Experiments are done in single core of Intel(R) Core(TM) i-4700MQ CPU @2.4 GHz, 8GB RAM, 64 bit Windows7 (CygWin64) 

- **DPLLCppSingleFileUsingSTL.cpp** : Benchmarks are picked up from [here](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html). For this experiment, uniform random 3-SAT *uf175-753 / uuf175-753: 175 variables, 753 clauses - 100 instances, all sat/unsat* is used. The benchmarks were run against MOMS,BIPOLAR-SUM,BIPOLAR-DIFF,BIPOLAR-PRODUCT,BIPOLAR-MAX heuristics choice (along with separately directional heuristics for either prioritizing unit-clause reduction or removal of clauses, indicated respectively as U and R suffixed algorithm name). Result of experiment indicated MOMS-R as best choice. Default heuristic value in DPLLCppSingleFileUsingSTL.cpp is set accordingly. Following tables are showing glimpse of the experiment for SAT and UNSAT benchmarks respectively.

|RESULT (timings are in micro-seconds) |MOMS-U	|MOMS-R	|BIPOLAR-SUM-U	|BIPOLAR-SUM-R	|BIPOLAR-DIFF-U	|BIPOLAR-DIFF-R	|BIPOLAR-PRODUCT-U	|BIPOLAR-PRODUCT-R	|BIPOLAR-MAX-U|	BIPOLAR-MAX-R|
|----|----|----|----|----|-----|----|----|-----|------|-------|
|Average	|152558.25	|86764.49	|179219.78	|106005.58	|2222266.61	|578982.62	|167039.11	|122296.57	|358540.05	|132837.14|
Standard-Deviation|91212.57869	|77473.21328	|110429.3019	|98794.14746	|1450788.913	|1008431.446	|108418.582	|115084.1983	|250385.5848	|158861.6208|
|MAX	|464026	|339019|	531030	|459026|	7025401|	6182353|	511029|	632036|	1551088|	719041|

|RESULT (timings are in micro-seconds) |MOMS-U	|MOMS-R	|BIPOLAR-SUM-U	|BIPOLAR-SUM-R	|BIPOLAR-DIFF-U	|BIPOLAR-DIFF-R	|BIPOLAR-PRODUCT-U	|BIPOLAR-PRODUCT-R	|BIPOLAR-MAX-U|	BIPOLAR-MAX-R|
|----|----|----|----|----|-----|----|----|-----|------|-------|
|Average	|274425.24	|274155.21	|329958.4	|329808.4	|4437793.41	|4436623.33	|326848.3	|326738.28	|535710.18	|536190.2|
Standard-Deviation|	82794.9593	|82756.40316	|114214.5186	|114283.0953	|2436453.04	|2435013.897	|115533.1071	|115238.8361|	201732.5983|	202200.4218|
|MAX	|487027	|482027	|685039	|687039	|12186697	|12189697	|768044	|759043	|1279073	|1278073|

As evident, direction heuristic does not matter much for UNSAT problem as the DPLL algorithm has to traverse complete searchspace anyways.


