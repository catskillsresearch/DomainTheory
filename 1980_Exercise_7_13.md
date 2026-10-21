# Exercise 7.13

Further combinators on the power domain are given in the exercises.

## EXERCISES

**EXERCISE 7.13.** Show that an effectively given domain can always be identified with a relation $\mathrm{INCL}(n,m)$ on integers, where the two derived relations

$$\mathrm{CONS}(n,m) \text{ iff } \exists k.\,\mathrm{INCL}(k,n) \text{ and } \mathrm{INCL}(k,m);$$

$$\mathrm{MEET}(n,m,k) \text{ iff } \forall j\,[\mathrm{INCL}(j,k) \text{ iff } \mathrm{INCL}(j,n) \text{ and } \mathrm{INCL}(j,m)]$$

are both recursively decidable, and where the following axioms hold:

(i) $\forall n.\,\mathrm{INCL}(n,n);$

(ii) $\forall n,m,k.\,\mathrm{INCL}(n,m)$ and $\mathrm{INCL}(m,k)$ imply $\mathrm{INCL}(n,k);$

(iii) $\exists m\,\forall n.\,\mathrm{INCL}(n,m)$

(iv) $\forall n,m.\,\mathrm{CONS}(n,m)$ implies $\exists k.\,\mathrm{MEET}(n,m,k).$

(Hint: Consider the neighbourhood system

$$\mathcal{D} = \big\{ \{m \in \mathbf{N} \mid \mathrm{INCL}(m,n)\} \mid n \in \mathbf{N} \big\}.$$

Is this essentially any effectively given system?)

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/CONS.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/CONS.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/InclStructure.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/InclStructure.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/MEET.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/MEET.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_i.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_i.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_ii.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_ii.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_iii.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_iii.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_iv.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_iv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/meet_iff_interEq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/meet_iff_interEq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/mem_ofPresentation_toNbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/mem_ofPresentation_toNbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/mem_toNbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/mem_toNbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_INCL.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_INCL.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_toNbhd_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_toNbhd_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_toPresentation_INCL.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_toPresentation_INCL.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconElem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconElem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconElemInv.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconElemInv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconIso.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconIso.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconstruct.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconstruct.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconstruct_isomorphic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconstruct_isomorphic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_inter_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_inter_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_subset_inter_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_subset_inter_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_top.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_top.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem_mem.lean)
