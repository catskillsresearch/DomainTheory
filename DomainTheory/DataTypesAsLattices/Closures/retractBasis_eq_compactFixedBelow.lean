/-ai
For a closure and a fixed point of its application, the retract basis of that fixed point equals the set of compact fixed points below it.

If a finite element is contained in the fixed point and the basis element is the closure applied to that finite element, monotonicity of application along the inclusion, rewritten by the fixed-point equation, puts the basis element below the fixed point. Conversely, if a value of the closure on a finite element lies below the fixed point, expansiveness of the closure puts the finite element inside that value, hence inside the fixed point.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.IsClosure
public import DomainTheory.DataTypesAsLattices.Closures.closure_expansive
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem retractBasis_eq_compactFixedBelow {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    retractBasis a x = compactFixedBelow a x := by
  ext k
  constructor
  · rintro ⟨n, hnx, hkn⟩
    refine ⟨⟨n, hkn⟩, ?_⟩
    rw [hkn]
    have := isScottContinuous_monotone (funOf_isScottContinuous a) hnx
    rwa [x.property] at this
  · rintro ⟨⟨n, hkn⟩, hkx⟩
    refine ⟨n, ?_, hkn⟩
    have hsub : funOf a (e n) ⊆ (x : Pomega) := by
      rwa [hkn] at hkx
    exact (closure_expansive ha (e n)).trans hsub

end DomainTheory.DataTypesAsLattices
