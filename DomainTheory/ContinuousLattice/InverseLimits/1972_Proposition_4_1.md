# Proposition 4.1

**4.1 Proposition.** Let $\langle D_n, j_n \rangle_{n=0}^{\infty}$ be an inverse system of continuous lattices where each $j_n : D_{n+1} \to D_n$ is a projection. Then the inverse limit space $D_{\infty}$ is also a continuous lattice.

**Proof:** We need only show that $D_{\infty}$ as a $T_0$-space is injective. So suppose $f_{\infty} : X \to D_{\infty}$ is given and $X \subseteq Y$. Define $f_n : X \to D_n$ by $f_n = j_{\infty n} \circ f_{\infty}$. Let $\bar{f}*n : Y \to D_n$ be the maximal extension of $f_n$ according to 3.8. Now we can see the point of Lemma 3.9: by this construction we guarantee that $\bar{f}n = j_n \circ \bar{f}{n+1}$. Hence the required $\bar{f}*{\infty} : Y \to D_{\infty}$ exists. $\square$

**Lean 4**

- [ContinuousLattice/InverseLimits/proposition_4_1.lean](DomainTheory/ContinuousLattice/InverseLimits/proposition_4_1.lean)
