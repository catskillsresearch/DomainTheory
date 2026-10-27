# Exercise 3.26

**EXERCISE 3.26.** Show that for every domain $D$ there is an approximable mapping

$$\mathrm{cond} : T \times D \times D \to D,$$

called the *conditional operator*, satisfying

(i) $\mathrm{cond}(\mathrm{true}, x, y) = x$

(ii) $\mathrm{cond}(\mathrm{false}, x, y) = y$

(iii) $\mathrm{cond}(\bot, x, y) = \bot$ .

(Hint: Recalling that $T = \{\{0\}, \{1\}, \{0, 1\}\}$, define cond as a relation by

$$
\begin{aligned}
0C \cup 10X \cup 110Y\ \mathrm{cond}\ Z \quad\text{iff}\quad & 0 \in C \text{ and } X \subseteq Z \text{ or} \\
& 1 \in C \text{ and } Y \subseteq Z \text{ or} \\
& 0, 1 \in C \text{ and } \Delta \subseteq Z ,
\end{aligned}
$$

<!-- page 54 -->

where $C \in T$ and $X \in D$ and $Y \in D$ and where we are using the construction of Exercise 3.14.) Find a similar operator in the domain

$$
T \times D_0 \times D_1 \to D_0 + D_1 .
$$

Show also there is an approximable mapping

$$
\mathrm{which} : D_0 + D_1 \to T
$$

such that for all $x \in |D_0 + D_1|$

$$
\mathrm{cond}(\mathrm{which}(x), \mathrm{in}_0(\mathrm{out}_0(x)), \mathrm{in}_1(\mathrm{out}_1(x))) = x .
$$

**[Exercise_3_26.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise_3_26.lean)**

@import "Exercise_3_26.lean"
