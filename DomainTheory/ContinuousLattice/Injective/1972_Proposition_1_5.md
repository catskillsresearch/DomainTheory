# Proposition 1.5

The relationship between arbitrary $T_0$-spaces and the injective spaces is given by the embedding theorem.

**1.5 Proposition.** Every $T_0$-space can be embedded in an injective space; in fact, in a Cartesian power of the 2-element space $\mathbb{O}$.

**Proof:** The proof is well known (cf. Čech (1966), Theorem 26B.9, p. 484.) But we give the argument for completeness sake. Let $X$ be the given space, and let $\mathfrak{O}$ be the class of open subsets of $X$. Let

$$
D = \mathbb{O}^{\mathfrak{O}}
$$

be the Cartesian power of $\mathbb{O}$. Then $D$ is injective by 1.3. Define the map $e: X \to D$ by:

$$
e(x)(U) = \begin{cases} \top & \text{if } x \in U,  \bot & \text{if } x \notin U, \end{cases}
$$

for $x \in X$ and $U \in \mathfrak{O}$. This map $e$ is continuous in view of the topology given to $\mathbb{O}$ and to $D$. The map $e$ is one-one, because $X$ is $T_0$. Finally, if $U \subseteq X$ is open, then

$$
\begin{aligned}
e(U) &= e(x) : x \in U 
&= e(x) : e(x)(U) = \top 
&= e(X) \cap t \in D : t(U) \in \top,
\end{aligned}
$$

which shows that the image $e(U)$ is open in the subspace $e(X) \subseteq D$. Therefore $e: X \to D$ is an embedding of $X$ as a subspace in $D$. $\square$

**Lean 4**

- [ContinuousLattice/Injective/isInjectiveSpace_sierpinski_power.lean](DomainTheory/ContinuousLattice/Injective/isInjectiveSpace_sierpinski_power.lean)
- [ContinuousLattice/Injective/proposition_1_5.lean](DomainTheory/ContinuousLattice/Injective/proposition_1_5.lean)
- [ContinuousLattice/Injective/t0_isEmbedding_into_sierpinski_power.lean](DomainTheory/ContinuousLattice/Injective/t0_isEmbedding_into_sierpinski_power.lean)
