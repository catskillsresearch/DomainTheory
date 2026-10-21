# Definition 1.1

**1.1 Definition.** A $T_0$-space $D$ is *injective* iff for arbitrary spaces $X$ and $Y$ if $X \subseteq Y$ as a subspace, then every continuous function $f: X \to D$ can be extended to a continuous function $\bar{f}: Y \to D$. As a diagram we have:

$$
\begin{gathered}
X \subseteq Y 
X \xrightarrow{f} D 
Y \xrightarrow{\bar{f}} D
\end{gathered}
$$

Some people will object to this terminology because I use the subspace relationship rather than a monomorphism in the category of $T_0$-spaces and continuous maps. However, only the trivial 1-point space is injective in the sense of monomorphisms in that category, and so the notion is uninteresting. If the reader prefers another terminology, I do not mind. As we shall see these spaces have very strong retraction properties.

**Injective space.** `IsInjectiveSpace` is this definition: every continuous map into the space extends along every topological embedding. [Proposition 2.11](../Constructions/1972_Proposition_2_11.md) proves a continuous lattice is injective, and [Theorem 2.12](../Theorem212/1972_Theorem_2_12.md) proves the two notions coincide.

**Lean 4**

- [ContinuousLattice/Injective/IsInjectiveSpace.lean](IsInjectiveSpace.lean)
