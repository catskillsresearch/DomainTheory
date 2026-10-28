module

public import Mathlib.Computability.Halting
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Order.CompleteLattice.Defs
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem enumerationUnion_left_isScottContinuous (y : Pomega) :
    IsScottContinuous (fun x => x ∪ y) := by
  constructor
  intro x
  ext n
  constructor
  · rintro (hn | hn)
    · exact mem_scottUnion.mpr ⟨2 ^ n,
        by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inl (by simp [e_pow2])⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hn⟩
  · intro hn
    obtain ⟨i, hi, hni⟩ := mem_scottUnion.mp hn
    exact hni.elim (fun h => Or.inl (hi h)) Or.inr

end DomainTheory.DataTypesAsLattices
