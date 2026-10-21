# Exercise 4.9

**EXERCISE 4.9.** Show that there is an approximable operator

$$
\Psi : ((D \to D) \to D) \to ((D \to D) \to D)
$$

such that for $\theta : (D \to D) \to D$ and $f : D \to D$ we have

$$
\Psi(\theta)(f) = f(\theta(f)).
$$

Prove further that $\mathrm{fix} : (D \to D) \to D$ is the *least* fixed point of $\Psi$.

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_apply.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_apply.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_fix.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_fix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_least.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_least.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/fix_eq_fixElement_bigPsi.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/fix_eq_fixElement_bigPsi.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/toApproxMap_toFilter_fixMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/toApproxMap_toFilter_fixMap.lean)
