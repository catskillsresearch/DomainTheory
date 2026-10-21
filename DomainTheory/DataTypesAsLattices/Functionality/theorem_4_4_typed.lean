/-ai
Scott 1976, Theorem 4.4 (ii). An element u lies in the range of a ⊗ b if and only if u is the sequence pair of its applications at the numerals 0 and 1, the zeroth component lies in the range of a, and the first component lies in the range of b.

If u is fixed by the product, the application law writes u as the sequence pair of the two retracted components, and the component laws show that those components are already fixed by a and by b. Conversely, the application law together with the two typing equations rebuilds u.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 4.4 (ii).** `u : a ⊗ b` iff `u = ⟨u₀, u₁⟩`
with `u₀ : a` and `u₁ : b`. -/
theorem theorem_4_4_typed {a b u : Pomega} :
    typed u (tensorR a b) ↔
      u = pairSeq (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
        typed (funOf u (ofNat 0)) a ∧ typed (funOf u (ofNat 1)) b := by
  constructor
  · intro hu
    have hpair : u =
        pairSeq (funOf a (funOf u (ofNat 0)))
          (funOf b (funOf u (ofNat 1))) := by
      simpa [typed, tensorR_app] using hu
    have h0 : funOf u (ofNat 0) = funOf a (funOf u (ofNat 0)) := by
      have := congrArg (fun w => funOf w (ofNat 0)) hpair
      simpa [pairSeq_app_zero] using this
    have h1 : funOf u (ofNat 1) = funOf b (funOf u (ofNat 1)) := by
      have := congrArg (fun w => funOf w (ofNat 1)) hpair
      simpa [pairSeq_app_one] using this
    refine ⟨hpair.trans (congr (congrArg pairSeq h0.symm) h1.symm), h0, h1⟩
  · intro ⟨hpair, ha, hb⟩
    change u = funOf (tensorR a b) u
    rw [tensorR_app, ← ha, ← hb, ← hpair]

end DomainTheory.DataTypesAsLattices
