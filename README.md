# toySat

This is a built-from-scratch solver for Boolean Satisfiability Problem.

Techniques implemented:

- Two-literal watching structure
- VSIDS heuristics
- 1UIP CDCL with nonchronological backtracking
- Clause minimization
- A dynamic restart policy

To run this SAT solver:
1. Building:
```
make
```
2. Running:
```
./toysat benchmarks/*.cnf
```
3. Plese refer to example benchmarks in **benchmarks** folder for the format of input .cnf file.
4. If the problem is satisfiable, *.sat will be generated.
