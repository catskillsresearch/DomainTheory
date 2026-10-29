# Exercise 1.27

**EXERCISE 1.27.** Further closure properties of domains can be proved for bounded sets. We say $X \subseteq |\mathcal{D}|$ is *bounded* iff for some $y \in |\mathcal{D}|$ we have $x \subseteq y$ for all $x \in X$. This $y$ is called an *upper bound*. We let

$$
\bigsqcup X = \bigcap \{y \in |\mathcal{D}| \mid x \subseteq y \text{ all } x \in X\}.
$$

Prove that if $X$ is bounded, then $\bigsqcup X$ is the *least upper bound* for $X$ in $|\mathcal{D}|$. Prove also: if $U, V \in \mathcal{D}$ are neighbourhoods, then $\{U, V\}$ is consistent in $\mathcal{D}$ iff $\{\uparrow U, \uparrow V\}$ is bounded in $|\mathcal{D}|$. (That is, boundedness is for elements what consistency is for neighbourhoods.) Prove finally with the aid of 1.18 that $X \subseteq |\mathcal{D}|$ is bounded iff every finite subset of $X$ is bounded.

<!-- page 24 -->

**[Exercise_1_27.lean](Exercise_1_27.lean)**

@import "Exercise_1_27.lean"
**[NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem_1_10.lean](Theorem_1_10.lean)**

@import "Theorem_1_10.lean"
**[NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise_1_21.lean](Exercise_1_21.lean)**

@import "Exercise_1_21.lean"
