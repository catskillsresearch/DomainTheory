/-ai
An index lies in the atom of a positive list and a negative list if and only if its neighbourhood is contained in every positive target and in no negative target.

Unfold the atom as the intersection of the positive index set with the set of indices avoiding every negative index set, and rewrite by membership in the positive index set and in an index set.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.mem_IPos

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)





theorem mem_DAtom {pos neg : List ℕ} {m : ℕ} :
    m ∈ DAtom P pos neg ↔ (∀ i ∈ pos, P.X m ⊆ P.X i) ∧ (∀ j ∈ neg, ¬ P.X m ⊆ P.X j) := by
  simp only [DAtom, Set.mem_inter_iff, mem_IPos, Set.mem_ofPred_eq, mem_idxSet]

end DomainTheory.NeighbourhoodSystems
