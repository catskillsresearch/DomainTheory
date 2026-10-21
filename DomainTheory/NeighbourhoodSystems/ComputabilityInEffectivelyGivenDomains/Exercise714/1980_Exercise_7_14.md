# Exercise 7.14

**EXERCISE 7.14.** (For recursive-function theorists.) Prove the statements after definition 7.2 about the existence of primitive recursive functions for showing things recursively enumerable. (Recall that a non-empty set is r.e. iff it is the range of a primitive recursive function.) Show also that every computable element $y \in |E|$ can be written

$$y = \bigcup \{ \uparrow Y_{t(i)} \mid i \in \mathbf{N} \},$$

where $t : \mathbf{N} \to \mathbf{N}$ is primitive recursive and where we may assume
$Y_{t(i+1)} \subseteq Y_{t(i)}$

for all $i \in \mathbf{N}$.

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714.lean](../Exercise714.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/repred_range_primrec.lean](repred_range_primrec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/repredu2082_exists_primrec_enum.lean](repredu2082_exists_primrec_enum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/tFun.lean](tFun.lean)
