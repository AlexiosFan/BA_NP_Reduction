# Notes from the previous reductions
  - Reduction definitions: NREST, *Polynomial_reduction.thy* *Reduction.thy* both in the repository of Karp21
  -  

# Notes from the documentation search
  ## reduction from vertex cover to exact cover 
  - [stackexchange](https://cs.stackexchange.com/questions/117658/how-to-prove-exact-cover-problem-is-np-complete-using-vertex-cover-problem)
  - [Latin square](https://ceur-ws.org/Vol-2638/paper26.pdf): reduction via the latin squares?

  ## reduction from 3-colorability to exact cover
  - Karp: a direct reduction from chromatic number
  - Cornell notes: a reduction from 3-colorability to chromatic numher, which probably suits the exsiting implementation, see literature at **page 17**, applicable approach: no worry about the type of the set

# Next meet time: 15.March, 10am.

## A polynomial reduction from 3SAT to Exact cover
Given a formula $F$,
  - indexing the variables occurred in the formula, let $x_n$ denotes the n-th variable
  - indexing the clauses occurred in the formula, let $c_i$ denotes the i-th variable
  - let $p_{ij}$ denotes the j-th atom in the i-th clause

The we construct a set $X$ and its collection $S$
  - $X = \lbrace x_n | x_n \in (\text{vars } F)\rbrace \cup \lbrace c_i | c_i \in F \rbrace \cup \lbrace p_{ij} | p_{ij} \in c_i \land c_i \in F \rbrace$
    </br>X includes all variables, all clauses and all atoms in $F$
  - $(x_n, \bot) = \lbrace x_n \rbrace \cup \lbrace p_{ij} | p_{ij} = \neg x_n \land p_{ij} \in c_i \land c_i \in F \rbrace$
  - $(x_n, \top) = \lbrace x_n \rbrace \cup \lbrace p_{ij} | p_{ij} = x_n \land p_{ij} \in c_i \land c_i \in F \rbrace$
  </br> bipartites the existence of $x_n$ by its positive or negative existence
  - $S = \lbrace \lbrace p_{ij} \rbrace | p_{ij} \in c_i \land c_i \in F \rbrace \cup \lbrace (x_n, \bot) | x_n \in (\text{vars } F) \rbrace 
         \cup \lbrace (x_n, \bot) | x_n \in (\text{vars } F) \rbrace  \cup \lbrace \lbrace c_i, p_{ij} \rbrace | c_i \in F \land p_{ij} \in c_i \rbrace$
    </br> S includes all elementary sets of atoms, all binary sets of a clause and one of its atoms, and all $(x_n, \bot)$ and
    $(x_n, \top)$.

Now we show that the construction is sound and complete:
  - Soundness: $M \models F \Longrightarrow S' \text{ covers } X$
    We construct an $S' \subseteq S$ by 
    1. to include all $x_n$, we include $(x_n, \neg M(x_n)) \in S'$
    2. to include all $C_i$, we include $\lbrace C_i, p_{ij} \rbrace$ for $M(p_{ij}) \equiv \top$,
       there is at least one such $p_{ij}$, for $M$ is model of $F$ and for all clauses $M \models C_i$
    3. in case there are more than on such $p_{ij}$, 
       we choose the smallest index $j$ and include all other atoms as elementary set \lbrace p_{ij} \rbrace 
    </br>
    Then we check for the correctness:
    1. each $x_n$ is covered in its $(x_n, \neg M(x_n))$
    2. each $C_i$ is covered in its $\lbrace C_i, p_{ij} \rbrace$
    3. each $p_{ij}$ is covered either in $(x_n, \neg M(x_n))$ if $M(p_{ij}) \equiv \bot$
      </br> or in $\lbrace C_i, p_{ij} \rbrace$ and $p_{ij}$ if $M(p_{ij}) \equiv \top$

  - Completeness: $S' \text{ covers } X \Longrightarrow M \models F$
    We firstly reconstruct the formula $F$ with the $(x_n, \bot)$ and $(x_n, \bot)$
    </br>
    Then construct a Model $M$: we check $(x_n, b_n)$ that are included in the $S'$, let $M(x_n) \equiv b_n$
    </br>
    Then we show that this is a model for $F$. It is sufficient to show that $M \models C_i$ and to show that 
    there is always a $p_{ij}$ s.t. $M(p_{ij}) \equiv \top$
    </br> This is trivial, for  each $p_{ij}$ in $\lbrace C_i, p_{ij} \rbrace$ is not included in any $(x_n, b_n) \in S'$. The reason is 
    by construction, $M(p'_{ij}) \equiv \bot$ for $p'_{ij} \in (x_n, b_n)$

Finally we show that the reduction is in the polynomial time w.r.t to the size of the formula.
  - let m denotes the amount of variables, n denotes the amount of clauses, k denotes the amount of atoms
  </br> by definition of **3SAT**, we have $m \leq 3n \land p \leq 3n$
  - The construction of $X$ requires to insert all elements mentioned above, i.e. $\mathcal{O}(m + n + k)$
  - The construction of $S$ requires to insert 
    1. all atoms, $\mathcal{O}(k)$
    2. all binary sets of a clause and one of its atoms, $\mathcal{O}(3n)$
    3. all $(x_n, \bot)$ and $(x_n, \top)$, $\mathcal{O}(mn)$, for we need to iterate all variables and clauses for construction
  
Hence in total, the reduction requires quadratic complexity.