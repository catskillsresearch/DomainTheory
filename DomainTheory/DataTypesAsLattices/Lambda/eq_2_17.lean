module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.minExtend
public import DomainTheory.DataTypesAsLattices.Lambda.maxExtend
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.Occurs
public import DomainTheory.DataTypesAsLattices.Lambda.rename
public import DomainTheory.DataTypesAsLattices.Lambda.curry2
public import DomainTheory.DataTypesAsLattices.Lambda.curry3
public import DomainTheory.DataTypesAsLattices.Lambda.ScottContinuousFin
public import DomainTheory.DataTypesAsLattices.Lambda.curryFin
public import DomainTheory.DataTypesAsLattices.Lambda.nestApplyFin
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.seq0
public import DomainTheory.DataTypesAsLattices.Lambda.seq1
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.relComp
public import DomainTheory.DataTypesAsLattices.Lambda.setSum
public import DomainTheory.DataTypesAsLattices.Lambda.topRec
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb
public import DomainTheory.DataTypesAsLattices.Lambda.abs
public import DomainTheory.DataTypesAsLattices.Lambda.erase
public import DomainTheory.DataTypesAsLattices.Lambda.FUN
public import DomainTheory.DataTypesAsLattices.Lambda.seqCons
public import DomainTheory.DataTypesAsLattices.Lambda.interStep
public import DomainTheory.DataTypesAsLattices.Lambda.interC
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
public import DomainTheory.DataTypesAsLattices.Lambda.seqShift
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStepBody
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt
public import DomainTheory.DataTypesAsLattices.Lambda.lamOmega
public import DomainTheory.DataTypesAsLattices.Lambda.primRecVal
public import DomainTheory.DataTypesAsLattices.Lambda.primRecHat
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStep
public import DomainTheory.DataTypesAsLattices.Lambda.Ymap
public import DomainTheory.DataTypesAsLattices.Lambda.Fofg
public import DomainTheory.DataTypesAsLattices.Lambda.Yterm
public import DomainTheory.DataTypesAsLattices.Lambda.termShift
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStepTerm
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStepTerm
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.interC_app
@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.17).** `x ∩ y = Y(λf λx λy. x ⊃ (y ⊃ 0, ⊥), f(x−1)(y−1)+1)(x)(y)`. -/
theorem eq_2_17 (x y : Pomega) :
    funOf (funOf interC x) y = x ∩ y := by
  have hmem : ∀ n x y, n ∈ funOf (funOf interC x) y ↔ n ∈ x ∩ y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y
      rw [interC.app]
      constructor
      · intro hn
        rcases hn with ⟨hL, h0x⟩ | ⟨⟨k, hk, rfl⟩, _t, _ht⟩
        · rcases hL with ⟨hk0, h0y⟩ | ⟨hbot, _⟩
          · simp [ofNat] at hk0; subst hk0
            exact ⟨h0x, h0y⟩
          · simp [botElem] at hbot
        · have hk' : k ∈ predSet x ∩ predSet y :=
            (ih k (Nat.lt_succ_self k) (predSet x) (predSet y)).mp hk
          exact ⟨hk'.1, hk'.2⟩
      · intro ⟨hnx, hny⟩
        cases n with
        | zero => exact Or.inl ⟨Or.inl ⟨rfl, hny⟩, hnx⟩
        | succ k =>
          refine Or.inr ⟨⟨k, ?_, rfl⟩, k, hnx⟩
          exact (ih k (Nat.lt_succ_self k) (predSet x) (predSet y)).mpr ⟨hnx, hny⟩
  ext n
  exact hmem n x y

end DomainTheory.DataTypesAsLattices
