# Description
This is the repository for the bachelor thesis on the NP-hardness of Exact Cover, Exact Hitting Set, 
Subset Sum, Partition, Knapsack and Zero-One Integer Programming. The work is done in Isabelle, 
on the basis of the [Karp21](https://github.com/rosskopfs/poly-reductions) project.

## How to use this project
It is suggested to view this project with Isabelle editors. 
To successfully run this project, make sure that you have Isabelle-2022 installed and added to path and 
downloaded Archive of Formal Proofs 
to the lastest version. 
Then there are a few steps to do 
1. Build the Karp21 session in direcotry `/poly-reduction/Karp21` with the command
```
  isabelle jedit -l HOL-Analysis Karp21/All_Reductions_Poly.thy &
```
2. Build the project in the original path with the command 
```
  isabelle jedit -d your_path_to_current_directory -l Karp21
```
Alternatively, it is also possible to replace `jedit` with `vscode` if that is your preferred editor.
3. Enjoy