/-ai
Scott 1976, (2.27). The primitive-recursive revaluation of a and f at x equals the dollar combinator applied to the least fixed point of the recursion step and then to x.

Equation (2.25) rewrites the right-hand side as sequence revaluation of that fixed point. At each index belonging to x, the two values agree by the fixed-point formula for the primitive-recursive value.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_25
public import DomainTheory.DataTypesAsLattices.Lambda.primRecVal_fix

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.27).** `p̂ = Y(λu λn∈ω. n ⊃ a, f(n−1)(u(n−1)))`. -/
theorem eq_2_27 (a f x : Pomega) :
    primRecHat a f x = funOf (funOf dollarC (fix (primRecStep a f))) x := by
  rw [eq_2_25]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    refine Set.mem_iUnion₂.mpr ⟨n, hn, ?_⟩
    simpa [primRecVal_fix] using hkn
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    refine Set.mem_iUnion₂.mpr ⟨n, hn, ?_⟩
    simpa [primRecVal_fix] using hkn

end DomainTheory.DataTypesAsLattices
