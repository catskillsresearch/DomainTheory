# Exercise 3.14

## Human-English

**EXERCISE 3.14.** For the most part we can assume that there is at most a countable number of tokens; thus, without loss of generality the underlying sets $\Delta_i$ of given systems $\mathcal{D}_i$ could be assumed to be subsets of $\Sigma^*$ where $\Sigma = \{0, 1\}$. (Any denumerable set would do.) Show that the product $\mathcal{D}_0 \times \mathcal{D}_1$ could be defined as the system over the set $0\Delta_0 \cup 1\Delta_1$ where

$$
\mathcal{D}_0 \times \mathcal{D}_1 = \{0X \cup 1Y \mid X \in \mathcal{D}_0 \text{ and } Y \in \mathcal{D}_1\}.
$$

In other words, the assumption of the disjointness of $\Delta_0$ and $\Delta_1$ is unnecessary. Give, therefore, the revised definition of $\langle x, y \rangle$ for elements, and prove that for a single system $\mathcal{D}$, there exists an approximable mapping

$$
\mathrm{diag} : \mathcal{D} \to \mathcal{D} \times \mathcal{D}
$$

where $\mathrm{diag}(x) = \langle x, x \rangle$ for all $x \in |\mathcal{D}|$. Also extend the definition to a product of $n$-factors

$$
\mathcal{D}_0 \times \mathcal{D}_1 \times \cdots \times \mathcal{D}_{n-1}
$$

which will be a system over the set

$$
\bigcup_{i < n} 1^i 0 \Delta_i.
$$

Note that for a 2-termed product we simplify $10\Delta_1$ to $1\Delta_1$.

## AI: Human-English to AI-Lean

**[Exercise_3_14.lean](Exercise_3_14.lean)**

@import "Exercise_3_14.lean"
