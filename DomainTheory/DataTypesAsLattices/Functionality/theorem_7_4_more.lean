module

public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Embedding.extend
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.mu_law
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.mem
public import DomainTheory.DataTypesAsLattices.Functionality.emptyE
public import DomainTheory.DataTypesAsLattices.Functionality.singletonE
public import DomainTheory.DataTypesAsLattices.Functionality.arrowE
public import DomainTheory.DataTypesAsLattices.Functionality.prodE
public import DomainTheory.DataTypesAsLattices.Functionality.sumE
public import DomainTheory.DataTypesAsLattices.Functionality.Ea
public import DomainTheory.DataTypesAsLattices.Functionality.kerE
public import DomainTheory.DataTypesAsLattices.Functionality.Nrel
public import DomainTheory.DataTypesAsLattices.Functionality.Nk
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC
public import DomainTheory.DataTypesAsLattices.Functionality.inrightC
public import DomainTheory.DataTypesAsLattices.Functionality.outleftC
public import DomainTheory.DataTypesAsLattices.Functionality.outrightC
public import DomainTheory.DataTypesAsLattices.Functionality.whichC
public import DomainTheory.DataTypesAsLattices.Functionality.outC
public import DomainTheory.DataTypesAsLattices.Functionality.pairMed
public import DomainTheory.DataTypesAsLattices.Functionality.Z
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb
public import DomainTheory.DataTypesAsLattices.Functionality.iterateE
public import DomainTheory.DataTypesAsLattices.Functionality.eraseTag
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinRel
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinGood
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinE
public import DomainTheory.DataTypesAsLattices.Functionality.Hinterp
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp
public import DomainTheory.DataTypesAsLattices.Functionality.Htyped
public import DomainTheory.DataTypesAsLattices.Functionality.expTag
public import DomainTheory.DataTypesAsLattices.Functionality.expPayload
public import DomainTheory.DataTypesAsLattices.Functionality.hApply
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion
public import DomainTheory.DataTypesAsLattices.Functionality.hVar
public import DomainTheory.DataTypesAsLattices.Functionality.hZero
public import DomainTheory.DataTypesAsLattices.Functionality.hPred
public import DomainTheory.DataTypesAsLattices.Functionality.hCond
public import DomainTheory.DataTypesAsLattices.Functionality.hApp
public import DomainTheory.DataTypesAsLattices.Functionality.HF
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun
public import DomainTheory.DataTypesAsLattices.Functionality.Hcomb
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_1
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ
public import DomainTheory.DataTypesAsLattices.Functionality.plotkin_finite_separation
public import DomainTheory.DataTypesAsLattices.Functionality.eraseTag
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinE_erase
public import DomainTheory.DataTypesAsLattices.Functionality.plotkin_function_related
public import DomainTheory.DataTypesAsLattices.Functionality.eq_7_18_eq
public import DomainTheory.DataTypesAsLattices.Functionality.eq_7_19
public import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
public import DomainTheory.DataTypesAsLattices.Functionality.normalized_finite_app
public import DomainTheory.DataTypesAsLattices.Functionality.Z_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Functionality.Z_isScottContinuous_right

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 7.4 (i).** `Zₙ : (A → A) → (A → A)`. -/
theorem theorem_7_4.i (A : RestrictedEquiv) (n : ℕ) :
    (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n) := by
  refine ⟨Zcomb.isGraph n, Zcomb.isGraph n, ?_⟩
  intro f f' hf
  refine ⟨Zcomb.app_isGraph n f, Zcomb.app_isGraph n f', ?_⟩
  intro x y hxy
  simpa [Zcomb.app2] using Z.rel A n hf.2.2 hxy

/-- Plotkin: if `z` is typed as an iterator and is extensional in its first
argument, then `z(f)(x)` is some iterate `fⁿ(x)`. -/
theorem theorem_7_4.plotkin (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z)
    (f x : Pomega) :
    ∃ n, funOf (funOf z f) x = Z n f x := by
  let f' : Pomega := graph (fun y => funOf f y)
  have hf'graph : f' = graph (fun y => funOf f' y) := by
    apply graph_ext
    intro y
    exact (beta (funOf.isScottContinuous f) y).symm
  let A := iterateE f' x
  have hf'mem : (arrowE A A).mem f' := by
    refine ⟨hf'graph, hf'graph, ?_⟩
    intro u v huv
    rcases huv with ⟨⟨n, rfl⟩, rfl⟩
    refine ⟨⟨n + 1, rfl⟩, rfl⟩
  have hzA : (arrowE (arrowE A A) (arrowE A A)).mem z := hz A
  have hzf : (arrowE A A).mem (funOf z f') :=
    (theorem_7_1 (arrowE A A) (arrowE A A)).2.1 hzA hf'mem
  have hx : A.mem x := ⟨⟨0, by simp [Z]⟩, rfl⟩
  have hval : A.mem (funOf (funOf z f') x) :=
    (theorem_7_1 A A).2.1 hzf hx
  obtain ⟨⟨n, hn⟩, _⟩ := hval
  refine ⟨n, ?_⟩
  have hηf : funOf z f = funOf z f' := hη f
  rw [hηf, hn, Z.graph_funOf]

theorem theorem_7_4.finite (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z)
    {n : ℕ}
    (hn : ∀ j, funOf (funOf z (graph (sigmaJ j))) {pair j 0} =
      ({pair j n} : Pomega))
    (p q : ℕ) :
    funOf (funOf z (e p)) (e q) = Z n (e p) (e q) := by
  let j := max p q + 1
  let gf := graph (fun y => funOf (e p) y)
  let gu := gf ∪ graph (sigmaJ j)
  have hfg : (arrowE
      (plotkinE p q j) (plotkinE p q j)).rel gf gu := by
    simpa [j, gf, gu] using plotkin_function_related p q
  have hzfg :
      (arrowE (plotkinE p q j) (plotkinE p q j)).rel
        (funOf z gf) (funOf z gu) :=
    (hz (plotkinE p q j)).2.2 gf gu hfg
  have hstart :
      (plotkinE p q j).rel (e q) (e q ∪ {pair j 0}) := by
    refine ⟨⟨0, Or.inl rfl⟩, ⟨0, Or.inr rfl⟩, ?_⟩
    exact Relation.EqvGen.rel _ _
      ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  have hout :
      (plotkinE p q j).rel
        (funOf (funOf z gf) (e q))
        (funOf (funOf z gu) (e q ∪ {pair j 0})) :=
    hzfg.2.2 _ _ hstart
  obtain ⟨r, hr⟩ := theorem_7_4.plotkin z hη hz gf (e q)
  obtain ⟨m, hm⟩ :=
    theorem_7_4.plotkin z hη hz gu (e q ∪ {pair j 0})
  have hleft :
      funOf (funOf z gf) (e q) = Z r (e p) (e q) := by
    rw [hr]
    exact Z.graph_funOf r (e p) (e q)
  have hright :
      funOf (funOf z gu) (e q ∪ {pair j 0}) =
        Z m (e p) (e q) ∪ {pair j m} := by
    rw [hm]
    simpa [j, gf, gu] using plotkin_finite_separation p q m
  have herase := plotkinE_erase hout
  have horbit : Z r (e p) (e q) = Z m (e p) (e q) := by
    rw [hleft, hright] at herase
    exact (eraseTag.Z_finite p q r).symm.trans
      (herase.trans (eraseTag.Z_finite_union p q m))
  have hsigmaSub :
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} ⊆
        funOf (funOf z gu) (e q ∪ {pair j 0}) := by
    exact mu_law
      (funOf.monotone_right z Set.subset_union_right)
      Set.subset_union_right
  have htag : pair j n ∈ Z m (e p) (e q) ∪ {pair j m} := by
    rw [← hright]
    apply hsigmaSub
    rw [hn j]
    simp
  have hnm : n = m := by
    rcases htag with hbad | htag
    · exact (Z.finite_no_tag p q m n (by simpa [j] using hbad)).elim
    · exact (pair_inj htag).2
  rw [hη (e p), hleft, horbit, ← hnm]

/-- Plotkin's independent successors force one common iterate count on all
tagged successor tests. -/
theorem theorem_7_4.sigma_index (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) :
    ∃ n, ∀ j,
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} =
        ({pair j n} : Pomega) := by
  obtain ⟨n, hn⟩ :=
    theorem_7_4.plotkin z hη hz (graph (sigmaJ 0)) {pair 0 0}
  refine ⟨n, ?_⟩
  intro j
  have hn' :
      funOf (funOf z (graph (sigmaJ 0))) {pair 0 0} =
        ({pair 0 n} : Pomega) := by
    rw [hn, eq_7_18_eq]
  by_cases hj : j = 0
  · subst j
    exact hn'
  obtain ⟨nj, hnj⟩ :=
    theorem_7_4.plotkin z hη hz (graph (sigmaJ j)) {pair j 0}
  have hnj' :
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} =
        ({pair j nj} : Pomega) := by
    rw [hnj, eq_7_18_eq]
  obtain ⟨k, hk⟩ := theorem_7_4.plotkin z hη hz
    (graph (sigmaJ 0) ∪ graph (sigmaJ j))
    (({pair 0 0} : Pomega) ∪ {pair j 0})
  have hk' :
      funOf
          (funOf z (graph (sigmaJ 0) ∪ graph (sigmaJ j)))
          (({pair 0 0} : Pomega) ∪ {pair j 0}) =
        ({pair 0 k} : Pomega) ∪ {pair j k} := by
    rw [hk, eq_7_19]
  have hmono0 :
      funOf (funOf z (graph (sigmaJ 0))) {pair 0 0} ⊆
        funOf
          (funOf z (graph (sigmaJ 0) ∪ graph (sigmaJ j)))
          (({pair 0 0} : Pomega) ∪ {pair j 0}) :=
    mu_law
      (funOf.monotone_right z Set.subset_union_left)
      Set.subset_union_left
  have hmonoj :
      funOf (funOf z (graph (sigmaJ j))) {pair j 0} ⊆
        funOf
          (funOf z (graph (sigmaJ 0) ∪ graph (sigmaJ j)))
          (({pair 0 0} : Pomega) ∪ {pair j 0}) :=
    mu_law
      (funOf.monotone_right z Set.subset_union_right)
      Set.subset_union_right
  have h0mem : pair 0 n ∈ ({pair 0 k} : Pomega) ∪ {pair j k} := by
    rw [← hk']
    apply hmono0
    rw [hn']
    simp
  have hjmem : pair j nj ∈ ({pair 0 k} : Pomega) ∪ {pair j k} := by
    rw [← hk']
    apply hmonoj
    rw [hnj']
    simp
  have hnk : n = k := by
    rcases h0mem with h0 | h0
    · exact (pair_inj h0).2
    · exact (hj ((pair_inj h0).1).symm).elim
  have hnjk : nj = k := by
    rcases hjmem with hj0 | hjj
    · exact (hj (pair_inj hj0).1).elim
    · exact (pair_inj hjj).2
  rw [hnj', hnjk, ← hnk]

theorem theorem_7_4.unique (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) :
    ∃ n, z = Zcomb n := by
  obtain ⟨n, hn⟩ := theorem_7_4.sigma_index z hη hz
  refine ⟨n, ?_⟩
  have hfinite (p : ℕ) :
      funOf z (e p) = funOf (Zcomb n) (e p) := by
    let gp := graph (fun y => funOf (e p) y)
    have hgpGraph : gp = graph (fun y => funOf gp y) := by
      apply graph_ext
      intro y
      exact (normalized_finite_app p y).symm
    have hgpMem : (arrowE emptyE emptyE).mem gp :=
      ⟨hgpGraph, hgpGraph, fun _ _ h => False.elim h⟩
    have hzgpGraph : funOf z gp = graph (fun y => funOf (funOf z gp) y) :=
      ((theorem_7_1 (arrowE emptyE emptyE) (arrowE emptyE emptyE)).2.1
        (hz emptyE) hgpMem).1
    have hzFiniteGraph :
        funOf z (e p) = graph (fun y => funOf (funOf z (e p)) y) := by
      rw [hη (e p)]
      exact hzgpGraph
    apply graph_funOf_ext hzFiniteGraph (Zcomb.app_isGraph n (e p))
    intro x
    have hright :
        IsScottContinuous (fun y => Z n (e p) y) :=
      Z.isScottContinuous_right n (e p)
    have hleft :
        IsScottContinuous (fun y => funOf (funOf z (e p)) y) :=
      funOf.isScottContinuous (funOf z (e p))
    have heq := congrFun
      (IsScottContinuous.determined hleft hright
        (fun q => theorem_7_4.finite z hη hz hn p q)) x
    simpa [Zcomb.app2] using heq
  have hall (f : Pomega) : funOf z f = funOf (Zcomb n) f := by
    let gf := graph (fun y => funOf f y)
    have hgfGraph : gf = graph (fun y => funOf gf y) := by
      apply graph_ext
      intro y
      exact (beta (funOf.isScottContinuous f) y).symm
    have hgfMem : (arrowE emptyE emptyE).mem gf :=
      ⟨hgfGraph, hgfGraph, fun _ _ h => False.elim h⟩
    have hzgfGraph : funOf z gf = graph (fun y => funOf (funOf z gf) y) :=
      ((theorem_7_1 (arrowE emptyE emptyE) (arrowE emptyE emptyE)).2.1
        (hz emptyE) hgfMem).1
    have hzfGraph :
        funOf z f = graph (fun y => funOf (funOf z f) y) := by
      rw [hη f]
      exact hzgfGraph
    apply graph_funOf_ext hzfGraph (Zcomb.app_isGraph n f)
    intro x
    have hleft :
        IsScottContinuous (fun g => funOf (funOf z g) x) :=
      theorem_1_3 (f := fun u => funOf u x) (g := funOf z)
        (funOf.isScottContinuous_left x)
        (funOf.isScottContinuous z)
    have hright : IsScottContinuous (fun g => Z n g x) :=
      Z.isScottContinuous_left n x
    have heq := congrFun
      (IsScottContinuous.determined hleft hright (fun p => by
        have := congrArg (fun w => funOf w x) (hfinite p)
        simpa [Zcomb.app2] using this)) f
    simpa [Zcomb.app2] using heq
  exact graph_funOf_ext (hz emptyE).1 (Zcomb.isGraph n) hall

end DomainTheory.DataTypesAsLattices
