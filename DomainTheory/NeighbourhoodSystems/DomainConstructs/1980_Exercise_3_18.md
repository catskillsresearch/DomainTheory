# Exercise 3.18

**EXERCISE 3.18.** Let $\mathcal{D}_0$ and $\mathcal{D}_1$ be neighbourhood systems over $\Delta_0$ and $\Delta_1$, where we again assume that these are subsets of $\Sigma^*$. We assume that in addition *no neighbourhood is empty*. Why is this possible without loss of generality?

Define the *sum system* by:

$$
\mathcal{D}_0 + \mathcal{D}_1 = \{\{\Lambda\} \cup 0\Delta_0 \cup 1\Delta_1\} \cup \{0X \mid X \in \mathcal{D}_0\} \cup \{1Y \mid Y \in \mathcal{D}_1\}.
$$

Prove that this is a neighbourhood system over $\{\Lambda\} \cup 0\Delta_0 \cup 1\Delta_1$. (Throwing in $\{\Lambda\}$ was not all that necessary, but note that $\mathcal{B} = \mathcal{B} + \mathcal{B}$, and this is an equality of sets not just an isomorphism of systems.)

Prove that in general there are mappings

$$
in_i : \mathcal{D}_i \to \mathcal{D}_0 + \mathcal{D}_1 \quad \text{and} \quad out_i : \mathcal{D}_0 + \mathcal{D}_1 \to \mathcal{D}_i,
$$

where $out_i \circ in_i = I_{\mathcal{D}_i}$. Where does the assumption $\emptyset \notin \mathcal{D}_i$ come in? How can these sums be generalized to $n$-terms? (Hint: As for products use sets $1^i 0 \Delta_i$.) Draw some pictures.

**[Exercise_3_18.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise_3_18.lean)**

@import "Exercise_3_18.lean"
