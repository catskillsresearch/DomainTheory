module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.pair_zero_zero
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- `0 ∉ G`, so `G` is a positive non-zero test. -/
theorem not_mem_zero_Gcomb : 0 ∉ Gcomb := by
  intro h
  rcases h with ⟨n, m, hm, hmem⟩
  have hnm : n = 0 ∧ m = 0 := by
    have : pair n m = 0 := hm.symm
    have : pair n m = pair 0 0 := by simpa [pair_zero_zero] using this
    exact pair_inj this
  rcases hnm with ⟨rfl, rfl⟩
  simp [e_zero, condSet] at hmem

end DomainTheory.DataTypesAsLattices
