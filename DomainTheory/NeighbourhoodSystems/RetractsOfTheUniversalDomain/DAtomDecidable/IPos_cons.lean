/-ai
The positive index set of a list with a given head and tail is the intersection of the index set of the head with the positive index set of the tail.

By extensionality, a constraint for every member of the extended list is a constraint for the head together with a constraint for every member of the tail, and conversely.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem IPos_cons (i : ℕ) (rest : List ℕ) :
    IPos P (i :: rest) = idxSet P.X i ∩ IPos P rest := by
  ext m
  simp only [IPos, Set.mem_ofPred_eq, List.mem_cons, mem_idxSet, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨h i (Or.inl rfl), fun j hj => h j (Or.inr hj)⟩
  · rintro ⟨hi, hrest⟩ j (rfl | hj)
    · exact hi
    · exact hrest j hj

end DomainTheory.NeighbourhoodSystems
