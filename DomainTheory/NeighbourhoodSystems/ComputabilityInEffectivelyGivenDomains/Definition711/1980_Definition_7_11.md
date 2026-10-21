# Definition 7.11

One of the main reasons that $\mathbb{P}\mathcal{D}$ is like a power domain is the possibility of forming "finite sets".

**DEFINITION 7.11.** For elements $x_0, \dots, x_{n-1} \in |D|$ we define

$$\{x_0, \dots, x_{n-1}\} = \{z \in \mathbb{P} D \mid \exists X_0 \in x_0 \dots \exists X_{n-1} \in x_{n-1}.\, \bigcup_{i<n} (\uparrow X_i) \subseteq z\}.$$

(Note, we could also write $\forall i < n.\, X_i \in z$.) $\square$

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711.lean](../Definition711.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDfinJoin.lean](PDfinJoin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDfinJoinSucc.lean](PDfinJoinSucc.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDfinJoinZero.lean](PDfinJoinZero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmemFinJoin.lean](PDmemFinJoin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmem_finJoin.lean](PDmem_finJoin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmem_finJoinZero.lean](PDmem_finJoinZero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmem_finJoin_iUnion.lean](PDmem_finJoin_iUnion.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDsingleton.lean](PDsingleton.lean)
