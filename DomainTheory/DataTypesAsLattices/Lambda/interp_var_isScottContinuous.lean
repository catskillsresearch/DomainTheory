module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.exists_e_cover_finite
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
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
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.envSet_comm

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Appendix lemma for Theorem 2.1: abstraction preserves continuity in the other variables. -/
theorem interp_var_isScottContinuous (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) := by
  induction t generalizing ρ i with
  | var j =>
    constructor
    intro x
    by_cases hj : j = i
    · subst hj
      simpa [interp, envSet, Function.update] using id_isScottContinuous.out x
    · simpa [interp, envSet, Function.update, hj] using (const_isScottContinuous (ρ j)).out x
  | zero =>
    constructor
    intro x
    simpa [interp] using (const_isScottContinuous (ofNat 0)).out x
  | succ t ih =>
    exact theorem_1_3 succSet_isScottContinuous (ih ρ i)
  | pred t ih =>
    exact theorem_1_3 predSet_isScottContinuous (ih ρ i)
  | cond z x y iz ix iy =>
    constructor
    intro w
    ext n
    simp only [interp]
    constructor
    · intro hn
      rcases hn with ⟨hnx, h0⟩ | ⟨hny, t, ht⟩
      · have : n ∈ scottUnion (fun v => interp x (envSet ρ i v)) w := by
          rw [← (ix ρ i).out w]; exact hnx
        obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp this
        have : 0 ∈ scottUnion (fun v => interp z (envSet ρ i v)) w := by
          rw [← (iz ρ i).out w]; exact h0
        obtain ⟨m', hm', h0m⟩ := mem_scottUnion.mp this
        refine mem_scottUnion.mpr ⟨m ||| m', e_or_of_subset hm hm', Or.inl ⟨?_, ?_⟩⟩
        · exact IsScottContinuous.monotone (ix ρ i)
            (by rw [e_or]; exact Set.subset_union_left) hnm
        · exact IsScottContinuous.monotone (iz ρ i)
            (by rw [e_or]; exact Set.subset_union_right) h0m
      · have : n ∈ scottUnion (fun v => interp y (envSet ρ i v)) w := by
          rw [← (iy ρ i).out w]; exact hny
        obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp this
        have : t + 1 ∈ scottUnion (fun v => interp z (envSet ρ i v)) w := by
          rw [← (iz ρ i).out w]; exact ht
        obtain ⟨m', hm', htm⟩ := mem_scottUnion.mp this
        refine mem_scottUnion.mpr ⟨m ||| m', e_or_of_subset hm hm', Or.inr ⟨?_, t, ?_⟩⟩
        · exact IsScottContinuous.monotone (iy ρ i)
            (by rw [e_or]; exact Set.subset_union_left) hnm
        · exact IsScottContinuous.monotone (iz ρ i)
            (by rw [e_or]; exact Set.subset_union_right) htm
    · intro hn
      obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp hn
      rcases hnm with ⟨hnx, h0⟩ | ⟨hny, t, ht⟩
      · exact Or.inl ⟨IsScottContinuous.monotone (ix ρ i) hm hnx,
          IsScottContinuous.monotone (iz ρ i) hm h0⟩
      · exact Or.inr ⟨IsScottContinuous.monotone (iy ρ i) hm hny, t,
          IsScottContinuous.monotone (iz ρ i) hm ht⟩
  | app u x iu ix =>
    constructor
    intro w
    ext n
    simp only [interp]
    constructor
    · intro ⟨p, hp, hpair⟩
      have : pair p n ∈ scottUnion (fun v => interp u (envSet ρ i v)) w := by
        rw [← (iu ρ i).out w]; exact hpair
      obtain ⟨m, hm, hpm⟩ := mem_scottUnion.mp this
      obtain ⟨s, hs⟩ := (e_finite p).exists_finset_coe
      have hall : ∀ t ∈ s, ∃ q, e q ⊆ w ∧ t ∈ interp x (envSet ρ i (e q)) := by
        intro t ht
        have ht' : t ∈ e p := by
          have : t ∈ (s : Set ℕ) := ht
          rwa [hs] at this
        have : t ∈ interp x (envSet ρ i w) := hp ht'
        have : t ∈ scottUnion (fun v => interp x (envSet ρ i v)) w := by
          rwa [← (ix ρ i).out w]
        exact mem_scottUnion.mp this
      obtain ⟨N, hN, hsN⟩ := exists_e_cover_finite (ix ρ i) s hall
      refine mem_scottUnion.mpr ⟨m ||| N, e_or_of_subset hm hN, p, ?_, ?_⟩
      · have : e p ⊆ interp x (envSet ρ i (e (m ||| N))) := by
          rw [← hs]
          intro t ht
          exact IsScottContinuous.monotone (ix ρ i)
            (by rw [e_or]; exact Set.subset_union_right) (hsN ht)
        exact this
      · exact IsScottContinuous.monotone (iu ρ i)
          (by rw [e_or]; exact Set.subset_union_left) hpm
    · intro hn
      obtain ⟨m, hm, p, hp, hpair⟩ := mem_scottUnion.mp hn
      exact ⟨p, subset_trans hp (IsScottContinuous.monotone (ix ρ i) hm),
        IsScottContinuous.monotone (iu ρ i) hm hpair⟩
  | lam j body ih =>
    by_cases hj : j = i
    · subst hj
      constructor
      intro w
      simpa [interp, envSet, Function.update] using
        (const_isScottContinuous (graph (fun v => interp body (envSet ρ j v)))).out w
    · have hmap : IsScottContinuous (fun w =>
          graph (fun v => interp body (envSet (envSet ρ i w) j v))) := by
        refine graph_const_isScottContinuous
          (fun w v => interp body (envSet (envSet ρ i w) j v)) ?_
        intro v
        have : (fun w => interp body (envSet (envSet ρ i w) j v)) =
            (fun w => interp body (envSet (envSet ρ j v) i w)) := by
          funext w; rw [envSet_comm hj]
        rw [this]
        exact ih (envSet ρ j v) i
      constructor
      intro w
      simpa [interp] using hmap.out w

end DomainTheory.DataTypesAsLattices
