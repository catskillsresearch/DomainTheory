module

public import DomainTheory.DataTypesAsLattices.Embedding
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

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


lemma exists_least_mem {a : Pomega} (hex : ∃ k, k ∈ a) :
    ∃ k, k ∈ a ∧ ∀ i < k, i ∉ a := by
  have : ∀ n, n ∈ a → ∃ k ≤ n, k ∈ a ∧ ∀ i < k, i ∉ a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases Classical.em (∀ i < n, i ∉ a) with hmin | hmin
      · exact ⟨n, le_rfl, hn, hmin⟩
      · obtain ⟨i, hi⟩ := not_forall.mp hmin
        have hi' : i < n := (Classical.not_imp.mp hi).1
        have hia : i ∈ a := not_not.mp (Classical.not_imp.mp hi).2
        obtain ⟨k, hki, hk, hall⟩ := ih i hi' hia
        exact ⟨k, hki.trans hi'.le, hk, hall⟩
  obtain ⟨n, hn⟩ := hex
  obtain ⟨k, _, hk, hall⟩ := this n hn
  exact ⟨k, hk, hall⟩

end DomainTheory.DataTypesAsLattices
