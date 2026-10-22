# Exercise 4.23

**EXERCISE 4.23.** (Suggested by S. Eilenberg). Suppose $f : \mathcal{D} \to \mathcal{D}$ is approximable on a given domain $\mathcal{D}$. Suppose $a_n : \mathcal{D} \to \mathcal{D}$ is a sequence of approximable maps where

(i) $a_0(x) = \bot$, for all $x \in |\mathcal{D}|$;

(ii) $a_n \sqsubseteq a_{n+1}$ in $\mathcal{D} \to \mathcal{D}$, for all $n \in \mathbf{N}$;

(iii) $\bigsqcup_{n=0}^{\infty} a_n = I_{\mathcal{D}}$ in $\mathcal{D} \to \mathcal{D}$;

(iv) $a_{n+1} \circ f = a_{n+1} \circ f \circ a_n$, for all $n \in \mathbf{N}$.

Prove that $f$ has a unique fixed point. (Hint: Show that if $x = f(x)$, then $a_n(x) \sqsubseteq a_n(\mathrm{fix}(f))$ for all $n \in \mathbf{N}$ by induction on $n$.)

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise423/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise423/f_unique_fixedPoint.lean](f_unique_fixedPoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise423.lean](../Exercise423.lean)
