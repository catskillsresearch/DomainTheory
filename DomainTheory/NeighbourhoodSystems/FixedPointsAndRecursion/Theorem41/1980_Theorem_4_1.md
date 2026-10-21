# Theorem 4.1

**THEOREM 4.1.** For any approximable mapping $f : D \to D$ on any domain, there exists a least element $x \in |D|$ where

$$
f(x) = x.
$$

**Proof:** Let $f^n$ for $n \in \mathbf{N}$ stand for the $n$-fold composition of $f$ with itself. That is,

$$
f^0 = I_D, \text{ and}
$$

$$
f^{n+1} = f \circ f^n.
$$

Define

$$
x = \{ X \in D \mid \Delta\ f^n\ X, \text{ for some } n \in \mathbf{N} \}.
$$

We see $X \in x$ iff there is a finite sequence $\Delta = X_0, X_1, \ldots, X_n = X$ where $X_i\ f\ X_{i+1}$ holds for all $i < n$. Now since $\Delta\ f\ \Delta$ automatically holds, a sequence for an $X \in x$ can always be extended to a longer sequence just by adding more $\Delta$'s on the front.

We want to prove $x \in |D|$. Clearly $\Delta \in x$; and if $X \subseteq Y$ and $X \in x$, then $Y \in x$. All that remains to be shown is the closure of $x$ under intersection. Note that if

$$
U\ f\ V \quad \text{and} \quad U'\ f\ V'
$$

hold and $U, U'$ are consistent in $D$, then $V$ and $V'$ are consistent and
$(U \cap U')\ f\ (V \cap V')$

must hold. Generalizing this to sequences, if

$$
\Delta = X_0\ f\ X_1\ f\ \cdots\ f\ X_n = X, \text{ and}
$$

$$
\Delta = Y_0\ f\ Y_1\ f\ \cdots\ f\ Y_n = Y
$$

both hold (and note we have arranged the lengths of the two sequences to be equal), then each pair $X_i, Y_i$ is consistent and we have

$$
\Delta = (X_0 \cap Y_0)\ f\ (X_1 \cap Y_1)\ f\ \cdots\ f\ (X_n \cap Y_n) = X \cap Y.
$$

This establishes the desired closure.

We also note that if $X \in x$ and $X\ f\ Y$ then $Y \in x$. Therefore, $f(x) \subseteq x$ and indeed by its very construction $x$ is the *least* element of $|D|$ with this property. (Why?) But $f$ is monotone, so $f(f(x)) \subseteq f(x)$; hence, $x = f(x)$. By what we have already said it must be the least such element. $\square$

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/comp_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/comp_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/exists_principal_iterMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/exists_principal_iterMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_eq_iSupDirected.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_eq_iSupDirected.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_le_of_toElementMap_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_le_of_toElementMap_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_eq_iSup.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_eq_iSup.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_fixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_fixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_least.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_least.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap_principal.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap_principal.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap_toFilter.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap_toFilter.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_unique.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem_eq_iterate.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem_eq_iterate.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_mono_map.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_mono_map.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iter_comm.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iter_comm.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/mem_fixElement.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/mem_fixElement.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/mem_iterElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/mem_iterElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/rel_master_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/rel_master_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/rel_master_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/rel_master_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/toElementMap_fixElement.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/toElementMap_fixElement.lean)
