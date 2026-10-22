# Definition 7.2

**DEFINITION 7.2.** Given two recursively presented domains,

$$\mathcal{D} = \{ X_n \mid n \in \mathbf{N} \} \text{ and } E = \{ Y_m \mid m \in \mathbf{N} \},$$

an approximable mapping $f : \mathcal{D} \to E$ is said to be *computable* iff the relation

$$X_n f Y_m$$

is recursively enumerable in $n$ and $m$. $\square$

The question to ask first is why "recursively enumerable" rather than "recursive" (= "recursively decidable")? The answer will become clear when we let $\mathcal{D}$ degenerate to the one-element domain, $\mathcal{D} = \{ \Delta \}$. Then what we are considering is merely a single element

$$y = f(\{ \Delta \}) \in |E|.$$

Therefore, 7.2 incorporates the notion of a *computable element* of a domain. And the condition reduces to the statement that the filter $y \in |E|$ is such that the set

$$\{ m \in \mathbf{N} \mid Y_m \in y \}$$

is a recursively enumerable set of integers. The point is that the elements of $|E|$ are finite or infinite. If $y$ were finite, the set of indices above would indeed be recursive in view of
our assumptions on $E$. But an infinite element can in general only be approximated "a little at a time". We cannot expect to know the whole story of its approximations in a flash. What it means to be recursively enumerable is that there is a primitive recursive function (hence, a total function), $r : \mathbf{N} \to \mathbf{N}$, such that

$$y = \{ Y_{r(i)} \mid i \in \mathbf{N} \}.$$

That is to say, *all* the approximations to $y$ can eventually be listed. In the case of the mapping $f$ we could write

$$f = \{ (X_{s(i)}, Y_{r(i)}) \mid i \in \mathbf{N} \},$$

for a suitable pair of primitive recursive functions $s$ and $r$.

Definitions 7.1 and 7.2 may very well irritate the person hearing them for the first time: instead of explaining computability in direct terms, the whole question is thrown into the lap of recursion theory! There are several answers. "You have to start somewhere" is one thing I always say. Recursion on the integers is a well-understood theory, and we shall not need the refined parts of the development, fortunately. In any case, our definitions apply to *many* domains of quite different structure, not just to the domain $\mathbf{N}$. And the next step we shall take is to show how to build up computable functions (and also effectively given domains) from simpler ones. Thus, often it will not be necessary to go back to the seemingly over-precise definitions involving the indices but to appeal to some broad general principles.

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/IsComputableElement.lean](IsComputableElement.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/IsComputableMap.lean](IsComputableMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/apply_isComputableElement.lean](apply_isComputableElement.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/comp_isComputable.lean](comp_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/idMap_isComputable.lean](idMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/principal_isComputableElement.lean](principal_isComputableElement.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72.lean](../Definition72.lean)
