/-ai
A point lies in the folded intersection of the basis neighbourhoods indexed by a finite set if and only if it lies in the master set and in every neighbourhood indexed by a member of the set.

The proof is by induction on the finite set. The empty intersection is the master set. At an insertion, the new intersection is the neighbourhood of the new index cut with the old intersection, and membership in the enlarged index set splits into the new index and the old set.
ai-/
module

public import Mathlib.Data.Finset.Fold
import all Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.interOf_insert

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

/-- Membership in the folded intersection. -/
theorem mem_interOf {u : Finset ι} {x : α} :
    x ∈ B.interOf u ↔ x ∈ B.system.master ∧ ∀ i ∈ u, x ∈ B.nbhd i := by
  induction u using Finset.induction with
  | empty =>
    simp [interOf_empty]
  | insert a s ha ih =>
    rw [B.interOf_insert ha, Set.mem_inter_iff, ih]
    constructor
    · rintro ⟨ha', hm, hs⟩
      refine ⟨hm, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha'
      · exact hs i hi
    · rintro ⟨hm, hall⟩
      exact ⟨hall a (Finset.mem_insert_self a s), hm,
        fun i hi => hall i (Finset.mem_insert_of_mem hi)⟩

end NbhdBasis

end DomainTheory.BridgeTheorems
