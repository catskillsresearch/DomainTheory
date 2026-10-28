
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.sucC
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.sucC_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem sucC_zero : funOf sucC zeroC = ofNat 1 := by
  rw [sucC.app]
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    simp [zeroC, ofNat] at hn
    subst hn
    simpa [ofNat] using hk
  · intro hk
    simp [ofNat] at hk
    exact ⟨0, rfl, hk⟩

end DomainTheory.DataTypesAsLattices
