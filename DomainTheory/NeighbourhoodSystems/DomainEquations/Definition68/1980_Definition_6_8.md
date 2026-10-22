# Definition 6.8

From 6.7 we see that if we are going to have initial algebras at all we have to satisfy the domain equation

$$
D \cong T(D).
$$

But generally that is not enough to assure that $D$ is initial. There is a condition that our functors satisfy, however, which guarantees the existence of homomorphisms.

**DEFINITION 6.8.** On the category of domains and strict approximable maps a functor $T$ is *continuous on maps* if for any systems $D$ and $E$ the induced mapping

$$
\lambda f.\, T(f) : (D \to_\bot E) \to (T(D) \to_\bot T(E))
$$

is approximable.

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/Definition68/ContinuousOnMapsu2eisStrict_map.lean](ContinuousOnMapsu2eisStrict_map.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/idEndofunctor.lean](idEndofunctor.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/idEndofunctor_obj.lean](idEndofunctor_obj.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/idEndofunctor_map.lean](idEndofunctor_map.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/ContinuousOnMaps.lean](ContinuousOnMaps.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/toStrictMap_toStrictFilter.lean](toStrictMap_toStrictFilter.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/continuousOnMaps_id.lean](continuousOnMaps_id.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68.lean](../Definition68.lean)
