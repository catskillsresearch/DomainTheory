module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.pair_zero_zero
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.condC_app2

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- `0 ∉ cond(x)(y)`, since `0 = (0,0)` and `e_0 ⊃ x, y = ⊥`. -/
theorem not_mem_zero_cond_graph (x y : Pomega) :
    0 ∉ funOf (funOf condC x) y := by
  intro h
  rw [condC_app2] at h
  rcases h with ⟨n, m, hm, hmem⟩
  have : pair n m = pair 0 0 := by
    simpa [pair_zero_zero] using hm.symm
  obtain ⟨rfl, rfl⟩ := pair_inj this
  simp [e_zero, condSet] at hmem

end DomainTheory.DataTypesAsLattices
