# Exercise 3.17

**EXERCISE 3.17.** Using the $\mathcal{B}$ and $\mathcal{T}$ of Example 2.3 show there is a one-one approximable mapping

$$
f : \mathcal{B} \to \mathcal{T}^\infty
$$

and another approximable mapping

$$
g : \mathcal{T}^\infty \to \mathcal{B}
$$

such that

$$
g \circ f = I_{\mathcal{B}} \quad \text{and} \quad f \circ g \subseteq I_{\mathcal{T}^\infty}.
$$

Are $\mathcal{B}$ and $\mathcal{T}^\infty$ isomorphic? Are $\mathcal{B}$ and $\mathcal{T} \times \mathcal{B}$ isomorphic?

**Lean 4**

- [NeighbourhoodSystems/DomainConstructs/Exercise317.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/T.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/T.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/T_nbhd_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/T_nbhd_nonempty.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/Token.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/Token.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/bitNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/bitNbhd.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/bitNbhd_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/bitNbhd_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/comparable_of_agree.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/comparable_of_agree.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/encSet.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/encSet.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_agree.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_agree.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_anti.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_anti.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_nil.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_nil.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/exists_not_mem_bitNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/exists_not_mem_bitNbhd.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/f.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/f.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/f_injective.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/f_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/fg_le_id.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/fg_le_id.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/fiber_encSet_none.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/fiber_encSet_none.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/fiber_encSet_some.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/fiber_encSet_some.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/g.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/g.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/gf_eq_id.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/gf_eq_id.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/mem_encSet.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/mem_encSet.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/prefix_of_encSet_subset.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/prefix_of_encSet_subset.lean)
