/-ai
Every set in the positive system equals the enumerated set at some index.

Membership supplies an expression whose denotation is the set and is nonempty. The index of that expression is the witness. Unfolding the enumeration, decoding inverts indexing, nonemptiness of the denotation makes the nonemptiness decision true, and simplification yields the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.index
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode_index
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.inS_iff_exists_denote
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem SsysX_surj {Y : Set (List Bool)} (hY : InS Y) : ∃ n, SsysX n = Y := by
  obtain ⟨e, he, hne⟩ := inS_iff_exists_denote.mp hY
  refine ⟨SExpr.index e, ?_⟩
  unfold SsysX
  rw [SExpr.decode_index e]
  have hne' : (denote e).Nonempty := he ▸ hne
  have hb : decideNonemptyB e = true := (decideNonemptyB_iff e).2 hne'
  simp [hb, he]

end Exercise722

end DomainTheory.NeighbourhoodSystems
