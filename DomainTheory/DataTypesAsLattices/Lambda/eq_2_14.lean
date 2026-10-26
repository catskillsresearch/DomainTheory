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
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.omega_first_recursion

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.14).** `⊥ = (λx. x(x))(λx. x(x))`. -/
theorem eq_2_14 :
    funOf (graph (fun x => funOf x x)) (graph (fun x => funOf x x)) = botElem := by
  have hω : omegaComb (graph fun x => x) = graph (fun x => funOf x x) := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨n, m, rfl, hm⟩
      rw [theorem_1_2_i id_isScottContinuous] at hm
      exact ⟨n, m, rfl, hm⟩
    · intro hp
      rcases hp with ⟨n, m, rfl, hm⟩
      refine ⟨n, m, rfl, ?_⟩
      rw [theorem_1_2_i id_isScottContinuous]
      exact hm
  rw [← hω, omega_first_recursion id_isScottContinuous]
  apply subset_antisymm
  · intro k hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    have : ∀ n, iterateBot (fun x => x) n = botElem := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp [iterateBot, ih]
    simp [this n] at hkn
  · intro k hk
    exact hk.elim


end DomainTheory.DataTypesAsLattices
