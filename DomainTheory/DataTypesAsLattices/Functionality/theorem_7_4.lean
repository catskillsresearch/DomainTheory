module

public import DomainTheory.DataTypesAsLattices.Enumeration.SumMed
public import DomainTheory.DataTypesAsLattices.Enumeration.Zcomb
import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_1
import DomainTheory.DataTypesAsLattices.Functionality.iterateE
import DomainTheory.DataTypesAsLattices.Lambda.graph_model
import DomainTheory.DataTypesAsLattices.Graph.mu_law
import DomainTheory.DataTypesAsLattices.Functionality.PlotkinHelpers
import DomainTheory.DataTypesAsLattices.Lambda.eq_2_9
import DomainTheory.DataTypesAsLattices.Graph.funOf_more
import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
import DomainTheory.DataTypesAsLattices.Graph.beta
import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def eraseTag (j : ℕ) (u : Pomega) : Pomega :=
  {p | p ∈ u ∧ ∀ k, p ≠ pair j k}

namespace eraseTag

theorem Z_finite (p q m : ℕ) :
    eraseTag (max p q + 1) (Z m (e p) (e q)) = Z m (e p) (e q) := by
  ext k
  constructor
  · exact fun hk => hk.1
  · intro hk
    exact ⟨hk, fun r hkr => Z.finite_no_tag p q m r (hkr ▸ hk)⟩

theorem Z_finite_union (p q m : ℕ) :
    eraseTag (max p q + 1)
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z m (e p) (e q) := by
  ext k
  constructor
  · intro ⟨hk, hnot⟩
    rcases hk with hk | hk
    · exact hk
    · exact (hnot m (by simpa using hk)).elim
  · intro hk
    exact ⟨Or.inl hk, fun r hkr => Z.finite_no_tag p q m r (hkr ▸ hk)⟩

end eraseTag


def plotkinGood (p q j : ℕ) (u : Pomega) : Prop :=
  ∃ m, u = Z m (e p) (e q) ∨
    u = Z m (e p) (e q) ∪ {pair j m}

def plotkinRel (p q j : ℕ) (u v : Pomega) : Prop :=
  ∃ m, (u = Z m (e p) (e q) ∧
      v = Z m (e p) (e q) ∪ {pair j m}) ∨
    (v = Z m (e p) (e q) ∧
      u = Z m (e p) (e q) ∪ {pair j m})

def plotkinE (p q j : ℕ) : RestrictedEquiv where
  rel u v :=
    plotkinGood p q j u ∧ plotkinGood p q j v ∧
      Relation.EqvGen (plotkinRel p q j) u v
  symm := by
    intro u v ⟨hu, hv, huv⟩
    exact ⟨hv, hu, Relation.EqvGen.symm _ _ huv⟩
  trans := by
    intro u v w ⟨hu, _hv, huv⟩ ⟨_hv', hw, hvw⟩
    exact ⟨hu, hw, Relation.EqvGen.trans _ _ _ huv hvw⟩

namespace plotkinE

theorem erase {p q : ℕ} {u v : Pomega}
    (h : (plotkinE p q (max p q + 1)).rel u v) :
    eraseTag (max p q + 1) u = eraseTag (max p q + 1) v := by
  rcases h with ⟨_hu, _hv, h⟩
  clear _hu _hv
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨m, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · rw [eraseTag.Z_finite, eraseTag.Z_finite_union]
      · rw [eraseTag.Z_finite, eraseTag.Z_finite_union]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem finite_separation (p q m : ℕ) :
    Z m
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1)))
        ((e q) ∪ {pair (max p q + 1) 0}) =
      Z m (e p) (e q) ∪ {pair (max p q + 1) m} := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Z, DomainTheory.DataTypesAsLattices.eq_2_9, ih]
      have hbeta :
          funOf (graph (fun y => funOf (e p) y))
              (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
            funOf (e p) (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) :=
        beta (funOf.isScottContinuous (e p)) _
      rw [hbeta, funOf.e_union_fresh p (max p q + 1) m _
        (Nat.lt_succ_of_le (Nat.le_max_left p q)), sigmaJ.app,
        sigmaJ.union_fresh (fun k => Z.finite_no_tag p q m k)]
      rfl

theorem function_related (p q : ℕ) :
    (arrowE
      (plotkinE p q (max p q + 1))
      (plotkinE p q (max p q + 1))).rel
        (graph (fun y => funOf (e p) y))
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1))) := by
  have hgf : graph (fun y => funOf (e p) y) =
      graph (fun y => funOf (graph (fun y => funOf (e p) y)) y) := by
    apply graph_ext
    intro y
    exact (beta (funOf.isScottContinuous (e p)) y).symm
  have hgu :
      graph (fun y => funOf (e p) y) ∪ graph (sigmaJ (max p q + 1)) =
        graph (fun y => funOf
          (graph (fun y => funOf (e p) y) ∪
            graph (sigmaJ (max p q + 1))) y) := by
    let F := fun y => funOf (e p) y ∪ sigmaJ (max p q + 1) y
    have hrep :
        graph (fun y => funOf (e p) y) ∪ graph (sigmaJ (max p q + 1)) =
          graph F := DomainTheory.DataTypesAsLattices.eq_2_10 _ _
    rw [hrep]
    congr 1
    funext y
    dsimp only [F]
    rw [← hrep]
    rw [DomainTheory.DataTypesAsLattices.eq_2_9, PlotkinHelpers.normalized_finite_app, sigmaJ.app]
  refine ⟨hgf, hgu, ?_⟩
  intro u v huv
  have herase := plotkinE.erase huv
  rcases huv.1 with ⟨r, hur | hur⟩
  <;> rcases huv.2.1 with ⟨s, hvs | hvs⟩
  all_goals
    subst u
    subst v
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      simpa [eraseTag.Z_finite] using herase
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y)) (Z r (e p) (e q)) =
          Z (r + 1) (e p) (e q) := by
      rw [PlotkinHelpers.normalized_finite_app]
      rfl
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q)) = Z (s + 1) (e p) (e q) :=
      PlotkinHelpers.finite_sigma_plain_app p q s
    rw [hleft, hright, ← hrs']
    exact ⟨⟨r + 1, Or.inl rfl⟩, ⟨r + 1, Or.inl rfl⟩,
      Relation.EqvGen.refl _⟩
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      exact (eraseTag.Z_finite p q r).symm.trans
        (herase.trans (eraseTag.Z_finite_union p q s))
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y)) (Z r (e p) (e q)) =
          Z (r + 1) (e p) (e q) := by
      rw [PlotkinHelpers.normalized_finite_app]
      rfl
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q) ∪ {pair (max p q + 1) s}) =
          Z (s + 1) (e p) (e q) ∪
            {pair (max p q + 1) (s + 1)} :=
      PlotkinHelpers.finite_sigma_union_app p q s
    rw [hleft, hright, hrs']
    exact ⟨⟨s + 1, Or.inl rfl⟩, ⟨s + 1, Or.inr rfl⟩,
      Relation.EqvGen.rel _ _
        ⟨s + 1, Or.inl ⟨rfl, rfl⟩⟩⟩
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      exact (eraseTag.Z_finite_union p q r).symm.trans
        (herase.trans (eraseTag.Z_finite p q s))
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y))
            (Z r (e p) (e q) ∪ {pair (max p q + 1) r}) =
          Z (r + 1) (e p) (e q) :=
      PlotkinHelpers.normalized_finite_fresh_app p q r
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q)) = Z (s + 1) (e p) (e q) :=
      PlotkinHelpers.finite_sigma_plain_app p q s
    rw [hleft, hright, ← hrs']
    exact ⟨⟨r + 1, Or.inl rfl⟩, ⟨r + 1, Or.inl rfl⟩,
      Relation.EqvGen.refl _⟩
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      simpa using (eraseTag.Z_finite_union p q r).symm.trans
        (herase.trans (eraseTag.Z_finite_union p q s))
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y))
            (Z r (e p) (e q) ∪ {pair (max p q + 1) r}) =
          Z (r + 1) (e p) (e q) :=
      PlotkinHelpers.normalized_finite_fresh_app p q r
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q) ∪ {pair (max p q + 1) s}) =
          Z (s + 1) (e p) (e q) ∪
            {pair (max p q + 1) (s + 1)} :=
      PlotkinHelpers.finite_sigma_union_app p q s
    rw [hleft, hright, hrs']
    exact ⟨⟨s + 1, Or.inl rfl⟩, ⟨s + 1, Or.inr rfl⟩,
      Relation.EqvGen.rel _ _
        ⟨s + 1, Or.inl ⟨rfl, rfl⟩⟩⟩

end plotkinE


theorem eq_7_18_eq (j m : ℕ) :
    Z m (graph (sigmaJ j)) {pair j 0} = ({pair j m} : Pomega) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc
      Z (m + 1) (graph (sigmaJ j)) {pair j 0}
        = funOf (graph (sigmaJ j)) (Z m (graph (sigmaJ j)) {pair j 0}) := rfl
      _ = sigmaJ j (Z m (graph (sigmaJ j)) {pair j 0}) := sigmaJ.app _ _
      _ = sigmaJ j {pair j m} := by rw [ih]
      _ = {pair j (m + 1)} := sigmaJ.succ_singleton j m

theorem eq_7_18_ne (j j' m : ℕ) (hne : j ≠ j') :
    Z (m + 1) (graph (sigmaJ j)) {pair j' 0} = botElem := by
  induction m with
  | zero =>
    calc
      Z 1 (graph (sigmaJ j)) {pair j' 0}
        = funOf (graph (sigmaJ j)) {pair j' 0} := rfl
      _ = sigmaJ j {pair j' 0} := sigmaJ.app _ _
      _ = botElem := sigmaJ.succ_ne j j' 0 hne
  | succ m ih =>
    calc
      Z (m + 1 + 1) (graph (sigmaJ j)) {pair j' 0}
        = funOf (graph (sigmaJ j))
            (Z (m + 1) (graph (sigmaJ j)) {pair j' 0}) := rfl
      _ = sigmaJ j (Z (m + 1) (graph (sigmaJ j)) {pair j' 0}) :=
          sigmaJ.app _ _
      _ = sigmaJ j botElem := by rw [ih]
      _ = botElem := sigmaJ.bot j

theorem eq_7_19 (j j' m : ℕ) :
    Z m (graph (sigmaJ j) ∪ graph (sigmaJ j'))
        (({pair j 0} : Pomega) ∪ {pair j' 0}) =
      ({pair j m} : Pomega) ∪ {pair j' m} := by
  by_cases h : j = j'
  · subst j'
    simp only [Set.union_self]
    exact eq_7_18_eq j m
  · induction m with
    | zero => rfl
    | succ m ih =>
      rw [Z, eq_2_9, ih, sigmaJ.app, sigmaJ.app,
        sigmaJ.pair_union j j' m h]
      rw [show sigmaJ j' (({pair j m} : Pomega) ∪ {pair j' m}) =
          ({pair j' (m + 1)} : Pomega) by
        simpa [Set.union_comm] using sigmaJ.pair_union j' j m (Ne.symm h)]

namespace theorem_7_4

theorem i (A : RestrictedEquiv) (n : ℕ) :
    (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n) := by
  refine ⟨Zcomb.isGraph n, Zcomb.isGraph n, ?_⟩
  intro f f' hf
  refine ⟨Zcomb.app_isGraph n f, Zcomb.app_isGraph n f', ?_⟩
  intro x y hxy
  simpa [Zcomb.app2] using Z.rel A n hf.2.2 hxy

theorem plotkin (z : Pomega)
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

theorem finite (z : Pomega)
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
    simpa [j, gf, gu] using plotkinE.function_related p q
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
    simpa [j, gf, gu] using plotkinE.finite_separation p q m
  have herase := plotkinE.erase hout
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

theorem sigma_index (z : Pomega)
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

theorem unique (z : Pomega)
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
      exact (PlotkinHelpers.normalized_finite_app p y).symm
    have hgpMem : (arrowE emptyE emptyE).mem gp :=
      ⟨hgpGraph, hgpGraph, fun _ _ h => False.elim h⟩
    have hzgpGraph : funOf z gp = graph (fun y => funOf (funOf z gp) y) :=
      ((theorem_7_1 (arrowE emptyE emptyE) (arrowE emptyE emptyE)).2.1
        (hz emptyE) hgpMem).1
    have hzFiniteGraph :
        funOf z (e p) = graph (fun y => funOf (funOf z (e p)) y) := by
      rw [hη (e p)]
      exact hzgpGraph
    apply funOf.ext_graph hzFiniteGraph (Zcomb.app_isGraph n (e p))
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
    apply funOf.ext_graph hzfGraph (Zcomb.app_isGraph n f)
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
  exact funOf.ext_graph (hz emptyE).1 (Zcomb.isGraph n) hall

end theorem_7_4

theorem theorem_7_4 :
    (∀ A n, (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n)) ∧
      ∀ z,
        (∀ f, funOf z f = funOf z (graph (fun y => funOf f y))) →
        (∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) →
        ∃ n, z = Zcomb n :=
  ⟨theorem_7_4.i, theorem_7_4.unique⟩

end DomainTheory.DataTypesAsLattices
