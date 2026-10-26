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
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb_app
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_diag_iUnion

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Scott's core induction proving that `ω(graph f)(ω(graph f))` is the
least fixed point of `f`. -/
theorem omega_first_recursion {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (omegaComb (graph f)) (omegaComb (graph f)) = fix f := by
  let d := omegaComb (graph f)
  have hd : ∀ x, funOf d x = f (funOf x x) := by
    intro x
    simp [d, omegaComb_app, theorem_1_2_i hf]
  have hθ : funOf d d = f (funOf d d) := hd d
  refine subset_antisymm ?_ ((theorem_1_4 hf).2 _ hθ.symm)
  intro m hm
  -- Scott's argument: reduce to `e_l ⊆ d → e_l ⬝ e_l ⊆ a` with `a = fix f`.
  let a := fix f
  have ha : f a = a := (theorem_1_4 hf).1
  have key : ∀ l, e l ⊆ d → funOf (e l) (e l) ⊆ a := by
    intro l
    induction l using Nat.strongRecOn with
    | ind l ih =>
      intro hld k hk
      obtain ⟨n, hn, hp⟩ := hk
      have hnlt : n < l := (pair_le_left n k).trans_lt (mem_e_lt hp)
      have hnd : e n ⊆ d := subset_trans hn hld
      have hna : funOf (e n) (e n) ⊆ a := ih n hnlt hnd
      -- `(n,k) ∈ e_l ⊆ d = λx. f(x x)`, so `k ∈ f(e n ⬝ e n)`
      have : k ∈ funOf d (e n) := ⟨n, subset_rfl, hld hp⟩
      have : k ∈ f (funOf (e n) (e n)) := by
        rwa [hd] at this
      have : k ∈ f a := IsScottContinuous.monotone hf hna this
      rwa [ha] at this
  rw [funOf_diag_iUnion] at hm
  obtain ⟨l, hl, hml⟩ := Set.mem_iUnion.mp hm
  exact key l hl hml

end DomainTheory.DataTypesAsLattices
