# Exercise 4.10

**EXERCISE 4.10.** Given a domain $D$ and an element $a \in |D|$, construct a domain $D_a$ where

$$
|D_a| = \{x \in |D| \mid x \sqsubseteq a\}.
$$

Show that if $f : D \to D$ is approximable, then $f$ can be restricted to an approximable map $f' : D_{\mathrm{fix}(f)} \to D_{\mathrm{fix}(f)}$ where $f'(x) = f(x)$ for all $x \in |D_{\mathrm{fix}(f)}|$. How many fixed points does $f'$ have in $|D_{\mathrm{fix}(f)}|$?

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_restrict.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_restrict.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/fixElement_below_unique.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/fixElement_below_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/le_of_embed_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/le_of_embed_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relIso.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relIso.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap_toElementMap_embed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap_toElementMap_embed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap_unique_fixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap_unique_fixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem_master.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem_master.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/restrict.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/restrict.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/restrict_embed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/restrict_embed.lean)
