# Injective spaces

**1. INJECTIVE SPACES.** All spaces are $T_0$-spaces, and we begin by defining a class of spaces to be called *injective*.

- [Definition 1.1](1972_Definition_1_1.md)
- [Proposition 1.2](1972_Proposition_1_2.md)
- [Proposition 1.3](1972_Proposition_1_3.md)
- [Proposition 1.4](1972_Proposition_1_4.md)
- [Proposition 1.5](1972_Proposition_1_5.md)
- [Corollary 1.6](1972_Corollary_1_6.md)
- [Corollary 1.7](1972_Corollary_1_7.md)

As a result of these very elementary considerations, the injective spaces could be called *absolute retracts*, if one remembers to modify the standard definitions by using *arbitrary* subspaces rather than just *closed* subspaces. Note too that it is easy to show that the only continuous maps $e: X \to Y$ for which the extension property

$$
\begin{gathered}
X \xrightarrow{e} Y 
X \xrightarrow{f} \mathbb{O} 
Y \xrightarrow{\bar{f}} \mathbb{O}
\end{gathered}
$$

could hold for *all* continuous $f: X \to \mathbb{O}$ are embeddings as subspaces.

Thus it would seem that we have a reasonably good initial grasp of the notion of injective spaces, but further constructions are considerably facilitated by the introduction of the lattice structure.

**Lean 4**

- [ContinuousLattice/Injective.lean](DomainTheory/ContinuousLattice/Injective.lean)
- [ContinuousLattice/Injective/Basic.lean](DomainTheory/ContinuousLattice/Injective/Basic.lean)
