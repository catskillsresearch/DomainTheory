# Exercise 8.26

**EXERCISE 8.26.** Discuss in more detail the "pay-off" for $U$, namely the translation of "untyped" $\lambda$-calculus into $U$ as shown by the equations at the end of the lecture after the proof of 8.9. In particular show how the whole of the **typed** $\lambda$-calculus can be retranslated back into $U$ with the aid of projections. (Hint: Whenever you want to write
$$
f : D_a \to D_b,
$$
write instead

$$f = b \circ f \circ a,$$

where $a$, $b$ are finitary projections. Whenever you want to form a $\lambda$-abstraction

$$\lambda x^{D_a}.\,\sigma,$$

where $\sigma$ is of type $D_b$, instead form

$$\lambda x.\, b(\sigma'[a(x)/x]),$$

where $\sigma'$ is the further translation of $\sigma$ into untyped $\lambda$-calculus. Be sure to show that this result "has the right type" in the sense defined above.)

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/Uapply.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/Uapply.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/Uapply_Ulam.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/Uapply_Ulam.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/Ulam.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/Ulam.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/translateAbs.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/translateAbs.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/translateAbs_idMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/translateAbs_idMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/translateAbs_sandwich.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/translateAbs_sandwich.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/translateApp_hasType.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise826/translateApp_hasType.lean)
