# Definition 6.13

The proof is left for the exercises.

**DEFINITION 6.13.** A functor $T$ is *monotone on domains* iff whenever $D \triangleleft E$, then not only do we have $T(D) \triangleleft T(E)$ but the projection pair $i, j$ of 6.12 is mapped to the same kind of projection pair $T(i), T(j)$. A monotone functor is *continuous on domains* iff whenever $E$ is a domain, then the mapping

$$
\lambda D.\, T(D) : \{D \mid D \triangleleft E\} \to \{D' \mid D' \triangleleft T(E)\}
$$

is approximable. $\square$
We can now state an existence theorem that covers in fairly wide generality the examples of this lecture.

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/Definition613/MonotoneAt.lean](MonotoneAt.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/MonotoneOnDomains.lean](MonotoneOnDomains.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/monotoneOnDomains_id.lean](monotoneOnDomains_id.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/continuousOnDomains_id.lean](continuousOnDomains_id.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/targetFam.lean](targetFam.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/ContinuousOnDomains.lean](ContinuousOnDomains.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613.lean](../Definition613.lean)
