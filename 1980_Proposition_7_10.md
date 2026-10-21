# Proposition 7.10

**PROPOSITION 7.10.** The power domain $\mathbb{P}\mathcal{D}$ is a neighbourhood system if $\mathcal{D}$ is, and it is effectively given if $\mathcal{D}$ is.

*Proof* : The system $\mathcal{D}^\dagger$ is a neighbourhood system as we just remarked; indeed it is a positive neighbourhood system. It is easy to prove that the closure of any positive system under finite unions is a neighbourhood system, because the resulting family of sets is closed under *all* finite intersections. (If we left out the empty union, the result would be a positive system.) The proof is obvious since intersection of sets distributes over finite union. So $\mathbb{P}\mathcal{D}$ is a neighbourhood system.

For the second half of the proposition, we just have to constructivize the previous argument. Thus, if

$$\mathcal{D} = \{ X_n \mid n \in \mathbb{N} \},$$

then the elements of $\mathbb{P}\mathcal{D}$ can be written as:

$$\bigcup_{i < q} (\downarrow X_{n_i}),$$
and hence are indexed by the finite sequences $\langle n_0, \dots, n_{q-1} \rangle$ of integers. Now one of the standard devices of recursion theory is to put the finite sequences of integers into a recursive one-one correspondence with the integers themselves. This is the start of the recursive presentation of $\mathbb{P}\mathcal{D}$, since it means we can list effectively all the required neighbourhoods.

Next consider an intersection

$$\bigcup_{i < q} (\downarrow X_{n_i}) \cap \bigcup_{j < r} (\downarrow X_{m_j}) = \bigcup_{\substack{i < q \\ j < r}} \downarrow (X_{n_i} \cap X_{m_j}) \, .$$

Some of the terms which are $\emptyset$ have to be thrown out — but this requires only a finite number of decisions all computable by assumption. Now we have to rewrite

$$X_{n_i} \cap X_{m_j} = X_{k_{ij}} \, ,$$

but the finding of $k_{ij}$ is also computable. *Finally*, we have to re-order the doubly indexed sequence into a singly indexed sequence of length $q \cdot r$, but this is easily seen to be computable also. Therefore, intersections can be "calculated".

It remains to be shown that equality between neighbourhoods in $\mathbb{P}\mathcal{D}$ is decidable. The question really comes down to deciding something like:

$$\downarrow X_k \subseteq \bigcup_{i < q} \downarrow X_{n_i} \, .$$

Now since $X_k \in \downarrow X_k$, we find that the above is just equivalent to:

$$\exists i < q \ldotp X_k \subseteq X_{n_i} \, .$$

By our assumptions on $\mathcal{D}$, this is decidable. (It is this part of the argument that required the passage to $\mathcal{D}^\dagger$. It does not seem to be generally true that the closure under finite unions of an effectively given system is again effectively given.) $\square$

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/NeighborhoodSystemu2ePowerDomain_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/NeighborhoodSystemu2ePowerDomain_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_biUnion_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_biUnion_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_exists_Ypd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_exists_Ypd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_exists_Ypd_aux.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_exists_Ypd_aux.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_upSet_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_upSet_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_upSet_inter_biUnion.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_upSet_inter_biUnion.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_def.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_def.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_cons_code.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_cons_code.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_def.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_def.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerInterCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerInterCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerfoldl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerfoldl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerstep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerstep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_interCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_interCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_interEq_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_interEq_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_isPDmem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_isPDmem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_outerfoldl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_outerfoldl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/eqCode_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/eqCode_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterCode_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterCode_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterStp_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/interCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/interCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/interCode_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/interCode_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/mem_UPX.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/mem_UPX.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/mem_Ypd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/mem_Ypd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/outerInterStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/outerInterStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/outerInterStp_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/outerInterStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_innerInterStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_innerInterStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_interCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_interCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_outerInterStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_outerInterStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/subCode_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/subCode_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSetUnion_cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSetUnion_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSetUnion_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSetUnion_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSet_inter_eq_empty_of_not_cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSet_inter_eq_empty_of_not_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSet_subset_Ypd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSet_subset_Ypd_iff.lean)
