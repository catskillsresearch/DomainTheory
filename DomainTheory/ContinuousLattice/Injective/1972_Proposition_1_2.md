# Proposition 1.2

A slightly less trivial example of an injective space is the 2-point space $\mathbb{O}$ with "points" $\bot$ and $\top$ where $\top$ is open but $\bot$ is not. (This space is sometimes called the *Sierpinski Space*.)

**1.2 Proposition.** The space $\mathbb{O}$ is injective.

**Proof:** As is obvious, the continuous maps $f: X \to \mathbb{O}$ are in a one-one correspondence with the open subsets of $X$ (consider $f^{-1}(\top)$). If $X \subseteq Y$ as a subspace, then an open subset of $X$ is the restriction of some open subset of $Y$. Thus any $f: X \to \mathbb{O}$ can be extended to $\bar{f}: Y \to \mathbb{O}$. $\square$

**Lean 4**

- [ContinuousLattice/Injective/isInjectiveSpace_sierpinski.lean](DomainTheory/ContinuousLattice/Injective/isInjectiveSpace_sierpinski.lean)
- [ContinuousLattice/Injective/proposition_1_2.lean](DomainTheory/ContinuousLattice/Injective/proposition_1_2.lean)
