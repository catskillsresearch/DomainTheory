# Exercise 4.8

**EXERCISE 4.8.** Suppose $f : D \to D$ and $S \subseteq |D|$ are such that

(i) $\bot \in S$;

(ii) $x \in S$ always implies $f(x) \in S$;

(iii) whenever $\{x_n\}_{n=0}^{\infty} \subseteq S$ and $x_n \sqsubseteq x_{n+1}$ for all $n$, then $\bigsqcup_{n=0}^{\infty} x_n \in S$.

Conclude that $\mathrm{fix}(f) \in S$. (This could be called the principle of *fixed-point induction*.) Apply the method to a set of the form

$$
S = \{x \in |D| \mid a(x) = b(x)\},
$$

where $a, b : D \to D$ are approximable, and where we know $a(\bot) = b(\bot)$, and $f \circ a = a \circ f$ and $f \circ b = b \circ f$.

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fixElement_eq_supChain.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fixElement_eq_supChain.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fix_induction.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fix_induction.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fix_induction_eq.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fix_induction_eq.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_monotone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/mem_supChain.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/mem_supChain.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/supChain.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/supChain.lean)
