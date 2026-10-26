module

public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.e_one
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_zero
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_one
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_isUpper
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.isOpen_memOpen
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_iff_isOpen
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottOpen
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset

public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen
public import DomainTheory.DataTypesAsLattices.Classification.charOpen
public import DomainTheory.DataTypesAsLattices.Classification.ScottG
public import DomainTheory.DataTypesAsLattices.Classification.ScottF
public import DomainTheory.DataTypesAsLattices.Classification.ScottB
public import DomainTheory.DataTypesAsLattices.Classification.IsScottGdelta
public import DomainTheory.DataTypesAsLattices.Classification.IsFcapG
public import DomainTheory.DataTypesAsLattices.Classification.IsFcapGdelta
public import DomainTheory.DataTypesAsLattices.Classification.IsBdelta
public import DomainTheory.DataTypesAsLattices.Classification.charTop
public import DomainTheory.DataTypesAsLattices.Classification.pairIndexed
public import DomainTheory.DataTypesAsLattices.Classification.oddEvenPack
public import DomainTheory.DataTypesAsLattices.Classification.fcapGdeltaPack
public import DomainTheory.DataTypesAsLattices.Classification.evenPart
public import DomainTheory.DataTypesAsLattices.Classification.oddPart
public import DomainTheory.DataTypesAsLattices.Classification.BooleanMemE
public import DomainTheory.DataTypesAsLattices.Classification.closedToZero
public import DomainTheory.DataTypesAsLattices.Classification.zeroPrime
public import DomainTheory.DataTypesAsLattices.Classification.uvU
public import DomainTheory.DataTypesAsLattices.Classification.uvV
public import DomainTheory.DataTypesAsLattices.Classification.ThreeValued
public import DomainTheory.DataTypesAsLattices.Classification.typicalG
public import DomainTheory.DataTypesAsLattices.Classification.typicalF
public import DomainTheory.DataTypesAsLattices.Classification.typicalGdelta
public import DomainTheory.DataTypesAsLattices.Classification.typicalFcapG
public import DomainTheory.DataTypesAsLattices.Classification.typicalFcapGdelta
public import DomainTheory.DataTypesAsLattices.Classification.typicalBdelta
public import DomainTheory.DataTypesAsLattices.Classification.typicalSigma11
public import DomainTheory.DataTypesAsLattices.Classification.typicalPi11
public import DomainTheory.DataTypesAsLattices.Classification.IsSigma11
public import DomainTheory.DataTypesAsLattices.Classification.Pi11

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem charOpen_isScottContinuous (U : Set Pomega) :
    IsScottContinuous (charOpen U) := by
  constructor
  intro x
  ext k
  constructor
  · intro ⟨hk0, n, hn, hne⟩
    exact mem_scottUnion.mpr ⟨n, hn, hk0, n, subset_rfl, hne⟩
  · intro hk
    obtain ⟨m, hm, hk0, n, hn, hne⟩ := mem_scottUnion.mp hk
    exact ⟨hk0, n, subset_trans hn hm, hne⟩


theorem isScottOpen_univ : IsScottOpen (Set.univ : Set Pomega) :=
  (isScottOpen_iff_isOpen _).mpr isOpen_univ

theorem isScottOpen_empty : IsScottOpen (∅ : Set Pomega) :=
  (isScottOpen_iff_isOpen _).mpr isOpen_empty

theorem isScottOpen_union {U V : Set Pomega} (hU : IsScottOpen U) (hV : IsScottOpen V) :
    IsScottOpen (U ∪ V) :=
  (isScottOpen_iff_isOpen _).mpr
    (((isScottOpen_iff_isOpen _).mp hU).union ((isScottOpen_iff_isOpen _).mp hV))

theorem isScottOpen_inter {U V : Set Pomega} (hU : IsScottOpen U) (hV : IsScottOpen V) :
    IsScottOpen (U ∩ V) :=
  (isScottOpen_iff_isOpen _).mpr
    (((isScottOpen_iff_isOpen _).mp hU).inter ((isScottOpen_iff_isOpen _).mp hV))

theorem isScottOpen_iUnion {ι : Type*} (U : ι → Set Pomega) (hU : ∀ i, IsScottOpen (U i)) :
    IsScottOpen (⋃ i, U i) :=
  (isScottOpen_iff_isOpen _).mpr (isOpen_iUnion fun i => (isScottOpen_iff_isOpen _).mp (hU i))

theorem mem_preimage_isScottOpen {f : Pomega → Pomega} (hf : IsScottContinuous f) (k : ℕ) :
    IsScottOpen {x | k ∈ f x} := by
  have : {x | k ∈ f x} = f ⁻¹' memOpen k := rfl
  rw [this, isScottOpen_iff_isOpen]
  exact IsOpen.preimage ((IsScottContinuous.iff_continuous f).mp hf) (isOpen_memOpen k)

theorem mem_isScottOpen_iff {U : Set Pomega} (hU : IsScottOpen U) {x : Pomega} :
    x ∈ U ↔ ∃ n, e n ⊆ x ∧ e n ∈ U := by
  constructor
  · intro hx
    obtain ⟨B, rfl⟩ := hU
    obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨n, hxn, Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩⟩
  · intro ⟨n, hn, hne⟩
    exact isScottOpen_isUpper hU hne hn


theorem charTop_isScottContinuous (U : Set Pomega) :
    IsScottContinuous (charTop U) := by
  constructor
  intro x
  ext k
  constructor
  · intro ⟨n, hn, hne⟩
    exact mem_scottUnion.mpr ⟨n, hn, n, subset_rfl, hne⟩
  · intro hk
    obtain ⟨m, hm, n, hn, hne⟩ := mem_scottUnion.mp hk
    exact ⟨n, subset_trans hn hm, hne⟩

theorem charTop_eq_top {U : Set Pomega} (hU : IsScottOpen U) (x : Pomega) :
    charTop U x = topElem ↔ x ∈ U := by
  constructor
  · intro h
    have : 0 ∈ charTop U x := by rw [h]; exact Set.mem_univ 0
    obtain ⟨n, hn, hne⟩ := this
    exact isScottOpen_isUpper hU hne hn
  · intro hx
    ext k
    constructor
    · intro _; trivial
    · intro _
      exact (mem_isScottOpen_iff hU).mp hx

theorem charTop_eq_bot {U : Set Pomega} (hU : IsScottOpen U) (x : Pomega) :
    charTop U x = botElem ↔ x ∉ U := by
  constructor
  · intro h hx
    have : charTop U x = topElem := (charTop_eq_top hU x).mpr hx
    rw [h] at this
    have : (0 : ℕ) ∈ (botElem : Pomega) := by
      rw [this]; exact Set.mem_univ 0
    exact (mem_botElem 0).mp this
  · intro hx
    ext k
    constructor
    · intro ⟨n, hn, hne⟩
      exact hx (isScottOpen_isUpper hU hne hn)
    · intro hk
      exact ((mem_botElem k).mp hk).elim

theorem charTop_eq_bot_of_closed {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    charTop Cᶜ x = botElem ↔ x ∈ C := by
  rw [charTop_eq_bot hC]
  simp


theorem pairIndexed_isScottContinuous (fs : ℕ → Pomega → Pomega)
    (hfs : ∀ n, IsScottContinuous (fs n)) :
    IsScottContinuous (pairIndexed fs) := by
  constructor
  intro x
  ext k
  constructor
  · intro ⟨n, m, hk, hm⟩
    have : m ∈ scottUnion (fs n) x := by rw [← (hfs n).out x]; exact hm
    obtain ⟨p, hp, hmp⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨p, hp, n, m, hk, hmp⟩
  · intro hk
    obtain ⟨p, hp, n, m, hk, hm⟩ := mem_scottUnion.mp hk
    exact ⟨n, m, hk, IsScottContinuous.monotone (hfs n) hp hm⟩


theorem oddEvenPack_isScottContinuous {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (oddEvenPack f g) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hk, hn⟩ | ⟨n, hk, hn⟩
    · have : n ∈ scottUnion f x := by rw [← hf.out x]; exact hn
      obtain ⟨p, hp, hnp⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨p, hp, Or.inl ⟨n, hk, hnp⟩⟩
    · have : n ∈ scottUnion g x := by rw [← hg.out x]; exact hn
      obtain ⟨p, hp, hnp⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨p, hp, Or.inr ⟨n, hk, hnp⟩⟩
  · intro hk
    obtain ⟨p, hp, h⟩ := mem_scottUnion.mp hk
    rcases h with ⟨n, hk, hn⟩ | ⟨n, hk, hn⟩
    · exact Or.inl ⟨n, hk, IsScottContinuous.monotone hf hp hn⟩
    · exact Or.inr ⟨n, hk, IsScottContinuous.monotone hg hp hn⟩


theorem evenPart_oddEven (f g : Pomega → Pomega) (x : Pomega) :
    evenPart (oddEvenPack f g x) = g x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨k, hk, hkn⟩ | ⟨k, hk, hkn⟩
    · have : 2 * n = 2 * k + 1 := hk
      omega
    · have : k = n := by
        have : 2 * n = 2 * k := hk
        omega
      simpa [this] using hkn
  · intro hn
    exact Or.inr ⟨n, rfl, hn⟩

theorem oddPart_oddEven (f g : Pomega → Pomega) (x : Pomega) :
    oddPart (oddEvenPack f g x) = f x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨k, hk, hkn⟩ | ⟨k, hk, hkn⟩
    · have : k = n := by
        have : 2 * n + 1 = 2 * k + 1 := hk
        omega
      simpa [this] using hkn
    · have : 2 * n + 1 = 2 * k := hk
      omega
  · intro hn
    exact Or.inl ⟨n, rfl, hn⟩

theorem oddEvenPack_subset {f g : Pomega → Pomega} {x : Pomega} {N M : ℕ}
    (hf : f x ⊆ {m | m < N}) (hg : g x ⊆ {m | m < M}) :
    oddEvenPack f g x ⊆ {k | k < 2 * Nat.max N M + 1} := by
  intro k hk
  rcases hk with ⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩
  · have hnN : n < N := hf hn
    have : n < Nat.max N M := lt_of_lt_of_le hnN (Nat.le_max_left _ _)
    exact Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left this (by decide : 0 < 2))
  · have hnM : n < M := hg hn
    have hlt : n < Nat.max N M := lt_of_lt_of_le hnM (Nat.le_max_right _ _)
    have : 2 * n < 2 * Nat.max N M + 1 :=
      Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (Nat.le_of_lt hlt))
    exact this

theorem finite_Iio_nat (N : ℕ) : ({m : ℕ | m < N}).Finite :=
  Set.Finite.ofFinset (Finset.range N) fun x => by simp

theorem finite_subsets_lt (N : ℕ) :
    ({y : Pomega | y ⊆ {m | m < N}}).Finite :=
  (finite_Iio_nat N).finite_subsets

theorem isBooleanOpen_of_closed {U : Set Pomega} (hU : IsScottOpen Uᶜ) :
    IsBooleanOpen U := by
  have h := (IsBooleanOpen.ofOpen hU).compl
  rwa [compl_compl] at h

theorem isBooleanOpen_of_fcapg {U : Set Pomega} (hU : IsFcapG U) : IsBooleanOpen U := by
  obtain ⟨C, O, hC, hO, rfl⟩ := hU
  exact (isBooleanOpen_of_closed hC).inter (IsBooleanOpen.ofOpen hO)

theorem isBooleanOpen_sUnion_finite {S : Set (Set Pomega)}
    (hS : S.Finite) (hU : ∀ U ∈ S, IsBooleanOpen U) :
    IsBooleanOpen (⋃₀ S) := by
  revert hU
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro
    simp
    exact IsBooleanOpen.ofOpen isScottOpen_empty
  | insert ha hs ih =>
    intro hUV
    rename_i a s
    simp [Set.sUnion_insert]
    exact (hUV a (Set.mem_insert a s)).union
      (ih fun u hu => hUV u (Set.mem_insert_of_mem a hu))


theorem booleanMemE_ofOpen {U : Set Pomega} (hU : IsScottOpen U) :
    BooleanMemE U := by
  refine ⟨charOpen U, 1, {ofNat 0}, charOpen_isScottContinuous U, ?_, ?_, ?_, ?_⟩
  · intro x k hk
    rcases hk with ⟨rfl, _⟩
    exact Nat.zero_lt_one
  · exact Set.finite_singleton _
  · intro e he
    simp [ofNat] at he
    subst he
    intro k hk
    simp at hk
    subst hk
    exact Nat.zero_lt_one
  · ext x
    constructor
    · intro hx
      change charOpen U x = ofNat 0
      ext k
      constructor
      · intro ⟨hk0, n, hn, hne⟩
        simp [ofNat, hk0]
      · intro hk
        simp [ofNat] at hk
        subst hk
        obtain ⟨n, hn, hne⟩ := (mem_isScottOpen_iff hU).mp hx
        exact ⟨rfl, n, hn, hne⟩
    · intro hx
      have : 0 ∈ charOpen U x := by
        have : charOpen U x = ofNat 0 := hx
        rw [this]; simp [ofNat]
      obtain ⟨_, n, hn, hne⟩ := this
      exact isScottOpen_isUpper hU hne hn

theorem booleanMemE_union {U V : Set Pomega}
    (hU : BooleanMemE U) (hV : BooleanMemE V) : BooleanMemE (U ∪ V) := by
  obtain ⟨f, N, E, hf, hfb, hEf, hEsub, rfl⟩ := hU
  obtain ⟨g, M, F, hg, hgb, hFf, hFsub, rfl⟩ := hV
  let N' := 2 * max N M + 1
  let E' : Set Pomega :=
    {y | y ⊆ {m | m < N'} ∧ (evenPart y ∈ F ∨ oddPart y ∈ E)}
  refine ⟨oddEvenPack f g, N', E',
    oddEvenPack_isScottContinuous hf hg, ?_, ?_, ?_, ?_⟩
  · intro x
    exact oddEvenPack_subset (hfb x) (hgb x)
  · have hpow := finite_subsets_lt N'
    exact hpow.subset fun y hy => hy.1
  · intro y hy; exact hy.1
  · ext x
    constructor
    · intro hx
      refine ⟨oddEvenPack_subset (hfb x) (hgb x), ?_⟩
      rw [evenPart_oddEven, oddPart_oddEven]
      rcases hx with h | h
      · exact Or.inr h
      · exact Or.inl h
    · intro hx
      have hx' := hx.2
      rw [evenPart_oddEven, oddPart_oddEven] at hx'
      rcases hx' with h | h
      · exact Or.inr h
      · exact Or.inl h

theorem booleanMemE_inter {U V : Set Pomega}
    (hU : BooleanMemE U) (hV : BooleanMemE V) : BooleanMemE (U ∩ V) := by
  obtain ⟨f, N, E, hf, hfb, hEf, hEsub, rfl⟩ := hU
  obtain ⟨g, M, F, hg, hgb, hFf, hFsub, rfl⟩ := hV
  let N' := 2 * max N M + 1
  let E' : Set Pomega :=
    {y | y ⊆ {m | m < N'} ∧ evenPart y ∈ F ∧ oddPart y ∈ E}
  refine ⟨oddEvenPack f g, N', E',
    oddEvenPack_isScottContinuous hf hg, ?_, ?_, ?_, ?_⟩
  · intro x
    exact oddEvenPack_subset (hfb x) (hgb x)
  · have hpow := finite_subsets_lt N'
    exact hpow.subset fun y hy => hy.1
  · intro y hy; exact hy.1
  · ext x
    constructor
    · intro hx
      refine ⟨oddEvenPack_subset (hfb x) (hgb x), ?_⟩
      rw [evenPart_oddEven, oddPart_oddEven]
      exact ⟨hx.2, hx.1⟩
    · intro hx
      have : evenPart (oddEvenPack f g x) ∈ F ∧
          oddPart (oddEvenPack f g x) ∈ E := ⟨hx.2.1, hx.2.2⟩
      rw [evenPart_oddEven, oddPart_oddEven] at this
      exact ⟨this.2, this.1⟩

theorem booleanMemE_compl {U : Set Pomega} (hU : BooleanMemE U) :
    BooleanMemE Uᶜ := by
  obtain ⟨f, N, E, hf, hfb, hEf, hEsub, rfl⟩ := hU
  let E' : Set Pomega := {y | y ⊆ {m | m < N} ∧ y ∉ E}
  refine ⟨f, N, E', hf, hfb, ?_, fun y hy => hy.1, ?_⟩
  · exact (finite_subsets_lt N).subset fun y hy => hy.1
  · ext x
    constructor
    · intro hx
      exact ⟨hfb x, hx⟩
    · intro hx
      exact hx.2

/-- **Scott 1976, Theorem 6.6 (The 𝔅 theorem).** -/
theorem theorem_6_6 :
    ∀ U, U ∈ ScottB ↔
      ∃ f, IsScottContinuous f ∧ ∃ E : Set Pomega,
        E.Finite ∧ (∀ e ∈ E, e.Finite) ∧ U = {x | f x ∈ E} := by
  intro U
  constructor
  · intro hU
    have : BooleanMemE U := by
      induction hU with
      | ofOpen hU => exact booleanMemE_ofOpen hU
      | union _ _ ihU ihV => exact booleanMemE_union ihU ihV
      | inter _ _ ihU ihV => exact booleanMemE_inter ihU ihV
      | compl _ ih => exact booleanMemE_compl ih
    obtain ⟨f, N, E, hf, hfb, hEf, hEsub, rfl⟩ := this
    refine ⟨f, hf, E, hEf, fun e he => (finite_Iio_nat N).subset (hEsub e he), rfl⟩
  · rintro ⟨f, hf, E, hE, hEfin, rfl⟩
    have : {x | f x ∈ E} = ⋃₀ ((fun e => {x | f x = e}) '' E) := by
      ext x
      constructor
      · intro hx
        exact ⟨{y | f y = f x}, ⟨f x, hx, rfl⟩, rfl⟩
      · intro hx
        obtain ⟨_, ⟨e, he, rfl⟩, hx'⟩ := hx
        have hxeq : f x = e := hx'
        change f x ∈ E
        rwa [hxeq]
    rw [this]
    refine isBooleanOpen_sUnion_finite (hE.image _) fun W hW => ?_
    obtain ⟨e, heE, rfl⟩ := hW
    have hefin : e.Finite := hEfin e heE
    have hopen : IsScottOpen {x | e ⊆ f x} := by
      have : {x | e ⊆ f x} = ⋂ k ∈ hefin.toFinset, {x | k ∈ f x} := by
        ext x
        constructor
        · intro hx
          exact Set.mem_iInter₂.mpr fun k hk => hx (hefin.mem_toFinset.mp hk)
        · intro hx k hk
          exact Set.mem_iInter₂.mp hx k (hefin.mem_toFinset.mpr hk)
      rw [this, isScottOpen_iff_isOpen]
      exact isOpen_biInter_finset fun k _ =>
        (isScottOpen_iff_isOpen _).mp (mem_preimage_isScottOpen hf k)
    have hclosed : IsScottOpen {x | f x ⊆ e}ᶜ := by
      have : {x | f x ⊆ e}ᶜ = ⋃ k, {x | k ∉ e ∧ k ∈ f x} := by
        ext x
        constructor
        · intro hx
          obtain ⟨k, hk, hke⟩ := Set.not_subset.mp hx
          exact Set.mem_iUnion.mpr ⟨k, ⟨hke, hk⟩⟩
        · intro hx
          obtain ⟨k, hke, hk⟩ := Set.mem_iUnion.mp hx
          intro hsub
          exact hke (hsub hk)
      rw [this]
      exact isScottOpen_iUnion _ fun k => by
        by_cases hke : k ∈ e
        · have : {x | k ∉ e ∧ k ∈ f x} = (∅ : Set Pomega) := by
            ext x; simp [hke]
          rw [this]; exact isScottOpen_empty
        · have : {x | k ∉ e ∧ k ∈ f x} = {x | k ∈ f x} := by
            ext x; simp [hke]
          rw [this]; exact mem_preimage_isScottOpen hf k
    exact isBooleanOpen_of_fcapg ⟨{x | f x ⊆ e}, {x | e ⊆ f x}, hclosed, hopen, by
      ext x
      constructor
      · intro hx
        have : f x = e := by
          have : f x ∈ ({e} : Set Pomega) := hx
          simpa using this
        exact ⟨this.subset, this.symm.subset⟩
      · intro hx
        have : f x = e := subset_antisymm hx.1 hx.2
        simp [this]⟩


/-- **Scott 1976, Theorem 6.7, equalizer → `B_δ`.**
`{x | f x = g x} = ⋂_n ({n ∈ f ∧ n ∈ g} ∪ {n ∉ f ∧ n ∉ g})`. -/
theorem theorem_6_7_of_equalizer :
    ∀ U, (∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
        U = {x | f x = g x}) → IsBdelta U := by
  rintro U ⟨f, g, hf, hg, rfl⟩
  refine ⟨fun n => {x | n ∈ f x ∧ n ∈ g x} ∪ {x | n ∉ f x ∧ n ∉ g x}, ?_, ?_⟩
  · intro n
    refine (IsBooleanOpen.ofOpen
      (isScottOpen_inter (mem_preimage_isScottOpen hf n)
        (mem_preimage_isScottOpen hg n))).union
      (isBooleanOpen_of_closed ?_)
    have : {x | n ∉ f x ∧ n ∉ g x}ᶜ = {x | n ∈ f x} ∪ {x | n ∈ g x} := by
      ext x
      constructor
      · intro hx
        have : ¬ (n ∉ f x ∧ n ∉ g x) := hx
        by_cases hfx : n ∈ f x
        · exact Or.inl hfx
        · by_cases hgx : n ∈ g x
          · exact Or.inr hgx
          · exact (this ⟨hfx, hgx⟩).elim
      · intro hx h
        rcases hx with hf' | hg'
        · exact h.1 hf'
        · exact h.2 hg'
    rw [this]
    exact isScottOpen_union (mem_preimage_isScottOpen hf n)
      (mem_preimage_isScottOpen hg n)
  · ext x
    constructor
    · intro h
      refine Set.mem_iInter.mpr fun n => ?_
      have heq : f x = g x := h
      by_cases hn : n ∈ f x
      · exact Or.inl ⟨hn, by rwa [← heq]⟩
      · exact Or.inr ⟨hn, by simpa [heq] using hn⟩
    · intro hx
      ext n
      have hn := Set.mem_iInter.mp hx n
      constructor
      · intro hfx
        rcases hn with ⟨_, hng⟩ | ⟨hnf, _⟩
        · exact hng
        · exact (hnf hfx).elim
      · intro hgx
        rcases hn with ⟨hnf, _⟩ | ⟨_, hng⟩
        · exact hnf
        · exact (hng hgx).elim

/-- **Scott 1976, Theorem 6.7, converse packing.**
A countable intersection of equalizers is again an equalizer, via
`pairIndexed`. -/
theorem theorem_6_7_iInter_equalizer (f g : ℕ → Pomega → Pomega)
    (hf : ∀ n, IsScottContinuous (f n)) (hg : ∀ n, IsScottContinuous (g n)) :
    ∃ F G, IsScottContinuous F ∧ IsScottContinuous G ∧
      {x | ∀ n, f n x = g n x} = {x | F x = G x} :=
  ⟨pairIndexed f, pairIndexed g,
    pairIndexed_isScottContinuous f hf, pairIndexed_isScottContinuous g hg, by
    ext x
    constructor
    · intro h
      ext k
      constructor
      · intro ⟨n, m, hk, hm⟩
        exact ⟨n, m, hk, by rwa [← h n]⟩
      · intro ⟨n, m, hk, hm⟩
        exact ⟨n, m, hk, by rwa [h n]⟩
    · intro h n
      ext m
      constructor
      · intro hm
        have : pair n m ∈ pairIndexed g x := by
          have : pair n m ∈ pairIndexed f x := ⟨n, m, rfl, hm⟩
          rwa [h] at this
        obtain ⟨n', m', heq, hm'⟩ := this
        obtain ⟨rfl, rfl⟩ := pair_inj heq
        exact hm'
      · intro hm
        have : pair n m ∈ pairIndexed f x := by
          have : pair n m ∈ pairIndexed g x := ⟨n, m, rfl, hm⟩
          rwa [← h] at this
        obtain ⟨n', m', heq, hm'⟩ := this
        obtain ⟨rfl, rfl⟩ := pair_inj heq
        exact hm'⟩

/-- Every `B_δ` written as a countable intersection of equalizers is itself
an equalizer of continuous maps. -/
theorem theorem_6_7_converse_of_equalizers (f g : ℕ → Pomega → Pomega)
    (hf : ∀ n, IsScottContinuous (f n)) (hg : ∀ n, IsScottContinuous (g n))
    {U : Set Pomega} (hU : U = {x | ∀ n, f n x = g n x}) :
    ∃ F G, IsScottContinuous F ∧ IsScottContinuous G ∧ U = {x | F x = G x} := by
  obtain ⟨F, G, hF, hG, h⟩ := theorem_6_7_iInter_equalizer f g hf hg
  exact ⟨F, G, hF, hG, hU.trans h⟩

/-- Union is Scott-continuous in the left argument. -/
theorem union_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => (x ∪ y : Pomega)) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with h | h
    · exact mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, h],
        Or.inl (by simp [e_pow2])⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr h⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with h | h
    · exact Or.inl (hn h)
    · exact Or.inr h

/-- Union is Scott-continuous in the right argument. -/
theorem union_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => (x ∪ y : Pomega)) := by
  constructor
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with h | h
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl h⟩
    · exact mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, h],
        Or.inr (by simp [e_pow2])⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with h | h
    · exact Or.inl h
    · exact Or.inr (hn h)


theorem closedToZero_isScottContinuous (C : Set Pomega) :
    IsScottContinuous (closedToZero C) :=
  theorem_1_3.tuple (f := fun a b => (a ∪ b : Pomega))
    union_isScottContinuous_left union_isScottContinuous_right
    (const_isScottContinuous (ofNat 0)) (charTop_isScottContinuous Cᶜ)


theorem uvU_mono_left {x x' y : Pomega} (h : x ⊆ x') : uvU x y ⊆ uvU x' y := by
  intro k hk
  rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
  · exact Or.inl ⟨rfl, hne.imp_left fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩
  · rcases h1 with h10 | ⟨⟨n, hn⟩, h0⟩
    · exact Or.inr ⟨rfl, Or.inl ⟨h h10.1, h10.2⟩⟩
    · exact Or.inr ⟨rfl, Or.inr ⟨⟨n, h hn⟩, h0⟩⟩

theorem uvU_mono_right {x y y' : Pomega} (h : y ⊆ y') : uvU x y ⊆ uvU x y' := by
  intro k hk
  rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
  · exact Or.inl ⟨rfl, hne.imp_right fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩
  · rcases h1 with ⟨h0, ⟨n, hn⟩⟩ | h10
    · exact Or.inr ⟨rfl, Or.inl ⟨h0, ⟨n, h hn⟩⟩⟩
    · exact Or.inr ⟨rfl, Or.inr ⟨h10.1, h h10.2⟩⟩

theorem uvV_mono_left {x x' y : Pomega} (h : x ⊆ x') : uvV x y ⊆ uvV x' y := by
  intro k hk
  rcases hk with hk0 | ⟨hk1, hpos⟩ | ⟨h0, ⟨n, hn⟩, h0y, hpy⟩
  · exact Or.inl hk0
  · exact Or.inr (Or.inl ⟨hk1, hpos.imp_left fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩)
  · exact Or.inr (Or.inr ⟨h h0, ⟨n, h hn⟩, h0y, hpy⟩)

theorem uvV_mono_right {x y y' : Pomega} (h : y ⊆ y') : uvV x y ⊆ uvV x y' := by
  intro k hk
  rcases hk with hk0 | ⟨hk1, hpos⟩ | ⟨h0, hpx, h0y, ⟨n, hn⟩⟩
  · exact Or.inl hk0
  · exact Or.inr (Or.inl ⟨hk1, hpos.imp_right fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩)
  · exact Or.inr (Or.inr ⟨h0, hpx, h h0y, ⟨n, h hn⟩⟩)

theorem uvU_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => uvU x y) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
    · rcases hne with ⟨n, hn⟩ | hy
      · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inl ⟨rfl, Or.inl ⟨n, by simp [e_pow2]⟩⟩⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl ⟨rfl, Or.inr hy⟩⟩
    · rcases h1 with ⟨h0, hp⟩ | ⟨⟨n, hn⟩, h0⟩
      · exact mem_scottUnion.mpr ⟨1, by simp [e_one, h0],
          Or.inr ⟨rfl, Or.inl ⟨by simp [e_one], hp⟩⟩⟩
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inr ⟨rfl, Or.inr ⟨⟨n, by simp [e_pow2]⟩, h0⟩⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact uvU_mono_left hm hkm

theorem uvU_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => uvU x y) := by
  constructor
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
    · rcases hne with hx | ⟨n, hn⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl ⟨rfl, Or.inl hx⟩⟩
      · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inl ⟨rfl, Or.inr ⟨n, by simp [e_pow2]⟩⟩⟩
    · rcases h1 with ⟨h0, ⟨n, hn⟩⟩ | ⟨hp, h0⟩
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inr ⟨rfl, Or.inl ⟨h0, ⟨n, by simp [e_pow2]⟩⟩⟩⟩
      · exact mem_scottUnion.mpr ⟨1, by simp [e_one, h0],
          Or.inr ⟨rfl, Or.inr ⟨hp, by simp [e_one]⟩⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact uvU_mono_right hm hkm

theorem uvV_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => uvV x y) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨rfl, hpos⟩ | ⟨h0, ⟨n, hn⟩, h0y, hpy⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk0⟩
    · rcases hpos with ⟨n, hn⟩ | hy
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inr (Or.inl ⟨rfl, Or.inl ⟨n, by simp [e_pow2]⟩⟩)⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e_zero],
          Or.inr (Or.inl ⟨rfl, Or.inr hy⟩)⟩
    · refine mem_scottUnion.mpr ⟨1 ||| 2 ^ (n + 1), e_or_of_subset
        (by simp [e_one, Set.singleton_subset_iff, h0])
        (by simp [e_pow2, Set.singleton_subset_iff, hn]), ?_⟩
      refine Or.inr (Or.inr ⟨?_, ⟨n, ?_⟩, h0y, hpy⟩)
      · simp [e_or, e_one]
      · simp [e_or, e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact uvV_mono_left hm hkm

theorem uvV_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => uvV x y) := by
  constructor
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨rfl, hpos⟩ | ⟨h0, hpx, h0y, ⟨n, hn⟩⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk0⟩
    · rcases hpos with hx | ⟨n, hn⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e_zero],
          Or.inr (Or.inl ⟨rfl, Or.inl hx⟩)⟩
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e_pow2, Set.singleton_subset_iff, hn],
          Or.inr (Or.inl ⟨rfl, Or.inr ⟨n, by simp [e_pow2]⟩⟩)⟩
    · refine mem_scottUnion.mpr ⟨1 ||| 2 ^ (n + 1), e_or_of_subset
        (by simp [e_one, Set.singleton_subset_iff, h0y])
        (by simp [e_pow2, Set.singleton_subset_iff, hn]), ?_⟩
      refine Or.inr (Or.inr ⟨h0, hpx, ?_, ⟨n, ?_⟩⟩)
      · simp [e_or, e_one]
      · simp [e_or, e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact uvV_mono_right hm hkm

theorem bot_ne_ofNat_zero : botElem ≠ ofNat 0 := by
  intro h
  have : (0 : ℕ) ∈ botElem := by rw [h]; simp [ofNat]
  exact (mem_botElem 0).mp this

theorem top_ne_ofNat_zero : topElem ≠ ofNat 0 := by
  intro h
  have : (1 : ℕ) ∈ ofNat 0 := by rw [← h]; exact Set.mem_univ 1
  simp [ofNat] at this

theorem zeroPrime_ne_ofNat_zero : zeroPrime ≠ ofNat 0 := by
  intro h
  have : (1 : ℕ) ∈ ofNat 0 := by
    have : (1 : ℕ) ∈ zeroPrime := Or.inr rfl
    rwa [h] at this
  simp [ofNat] at this

theorem zeroPrime_ne_top : zeroPrime ≠ topElem := by
  intro h
  have : (2 : ℕ) ∈ zeroPrime := by rw [h]; exact Set.mem_univ 2
  simp [zeroPrime, ofNat] at this

theorem uvU_bot_bot : uvU botElem botElem = botElem := by
  ext k
  simp [uvU, botElem]

theorem uvV_bot_bot : uvV botElem botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with ⟨n, hn⟩ | ⟨n, hn⟩ <;> exact ((mem_botElem (n + 1)).mp hn).elim
    · exact ((mem_botElem 0).mp htop.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem ofNat_zero_nonempty : (ofNat 0).Nonempty :=
  ⟨0, rfl⟩

theorem ofNat_zero_not_pos : ¬ ∃ n, n + 1 ∈ ofNat 0 := by
  intro ⟨n, hn⟩
  simp [ofNat] at hn

theorem uvU_bot_zero : uvU botElem (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨h0, _⟩ | ⟨⟨n, hn⟩, _⟩
      · exact ((mem_botElem 0).mp h0).elim
      · exact ((mem_botElem (n + 1)).mp hn).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inr ofNat_zero_nonempty⟩

theorem uvV_bot_zero : uvV botElem (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with ⟨n, hn⟩ | hp
      · exact ((mem_botElem (n + 1)).mp hn).elim
      · exact (ofNat_zero_not_pos hp).elim
    · exact ((mem_botElem 0).mp htop.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem uvU_zero_bot : uvU (ofNat 0) botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨_, ⟨n, hn⟩⟩ | ⟨⟨n, hn⟩, _⟩
      · exact ((mem_botElem (n + 1)).mp hn).elim
      · exact (ofNat_zero_not_pos ⟨n, hn⟩).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inl ofNat_zero_nonempty⟩

theorem uvV_zero_bot : uvV (ofNat 0) botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨_, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with hp | ⟨n, hn⟩
      · exact (ofNat_zero_not_pos hp).elim
      · exact ((mem_botElem (n + 1)).mp hn).elim
    · exact ((mem_botElem 0).mp htop.2.2.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem uvU_zero_zero : uvU (ofNat 0) (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨_, hp⟩ | ⟨hp, _⟩
      · exact (ofNat_zero_not_pos hp).elim
      · exact (ofNat_zero_not_pos hp).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inl ofNat_zero_nonempty⟩

theorem uvV_zero_zero : uvV (ofNat 0) (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨_, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with hp | hp
      · exact (ofNat_zero_not_pos hp).elim
      · exact (ofNat_zero_not_pos hp).elim
    · exact (ofNat_zero_not_pos htop.2.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem top_pos : ∃ n, n + 1 ∈ topElem :=
  ⟨0, Set.mem_univ 1⟩

theorem uvU_bot_top : uvU botElem topElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨h0, _⟩ | ⟨⟨n, hn⟩, _⟩
      · exact ((mem_botElem 0).mp h0).elim
      · exact ((mem_botElem (n + 1)).mp hn).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inr ⟨0, Set.mem_univ 0⟩⟩

theorem uvV_bot_top : uvV botElem topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact ((mem_botElem 0).mp htop.1).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inr top_pos⟩)

theorem uvU_top_bot : uvU topElem botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨_, ⟨n, hn⟩⟩ | ⟨_, h0⟩
      · exact ((mem_botElem (n + 1)).mp hn).elim
      · exact ((mem_botElem 0).mp h0).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inl ⟨0, Set.mem_univ 0⟩⟩

theorem uvV_top_bot : uvV topElem botElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact ((mem_botElem 0).mp htop.2.2.1).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inl top_pos⟩)

theorem uvU_zero_top : uvU (ofNat 0) topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, _⟩
    · exact Or.inl hk0
    · exact Or.inr hk1
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl ⟨hk0, Or.inr ⟨0, Set.mem_univ 0⟩⟩
    · exact Or.inr ⟨hk1, Or.inl ⟨rfl, top_pos⟩⟩

theorem uvV_zero_top : uvV (ofNat 0) topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact (ofNat_zero_not_pos htop.2.1).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inr top_pos⟩)

theorem uvU_top_zero : uvU topElem (ofNat 0) = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, _⟩
    · exact Or.inl hk0
    · exact Or.inr hk1
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl ⟨hk0, Or.inl ⟨0, Set.mem_univ 0⟩⟩
    · exact Or.inr ⟨hk1, Or.inr ⟨top_pos, rfl⟩⟩

theorem uvV_top_zero : uvV topElem (ofNat 0) = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact (ofNat_zero_not_pos htop.2.2.2).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inl top_pos⟩)

theorem uvU_top_top : uvU topElem topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, _⟩
    · exact Or.inl hk0
    · exact Or.inr hk1
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl ⟨hk0, Or.inl ⟨0, Set.mem_univ 0⟩⟩
    · exact Or.inr ⟨hk1, Or.inl ⟨Set.mem_univ 0, top_pos⟩⟩

theorem uvV_top_top : uvV topElem topElem = topElem := by
  ext k
  constructor
  · intro _; exact Set.mem_univ k
  · intro _
    exact Or.inr (Or.inr ⟨Set.mem_univ 0, top_pos, Set.mem_univ 0, top_pos⟩)

/-- On `{⊥, 0, ⊤}`, `u(x)(y) = v(x)(y)` iff `x = 0` or `y = 0`. -/
theorem uv_eq_iff {x y : Pomega} (hx : ThreeValued x) (hy : ThreeValued y) :
    uvU x y = uvV x y ↔ x = ofNat 0 ∨ y = ofNat 0 := by
  rcases hx.out with rfl | rfl | rfl <;> rcases hy.out with rfl | rfl | rfl
  · simp [uvU_bot_bot, uvV_bot_bot, bot_ne_ofNat_zero]
  · simp [uvU_bot_zero, uvV_bot_zero]
  · constructor
    · intro h
      rw [uvU_bot_top, uvV_bot_top] at h
      exact (zeroPrime_ne_ofNat_zero h.symm).elim
    · intro h
      rcases h with h | h
      · exact (bot_ne_ofNat_zero h).elim
      · exact (top_ne_ofNat_zero h).elim
  · simp [uvU_zero_bot, uvV_zero_bot]
  · simp [uvU_zero_zero, uvV_zero_zero]
  · simp [uvU_zero_top, uvV_zero_top]
  · constructor
    · intro h
      rw [uvU_top_bot, uvV_top_bot] at h
      exact (zeroPrime_ne_ofNat_zero h.symm).elim
    · intro h
      rcases h with h | h
      · exact (top_ne_ofNat_zero h).elim
      · exact (bot_ne_ofNat_zero h).elim
  · simp [uvU_top_zero, uvV_top_zero]
  · constructor
    · intro h
      rw [uvU_top_top, uvV_top_top] at h
      exact (zeroPrime_ne_top h).elim
    · intro h
      rcases h with h | h <;> exact (top_ne_ofNat_zero h).elim

theorem charOpen_three (U : Set Pomega) (x : Pomega) :
    ThreeValued (charOpen U x) := by
  constructor
  by_cases h : 0 ∈ charOpen U x
  · refine Or.inr (Or.inl ?_)
    ext k
    constructor
    · intro ⟨hk0, _⟩; simp [ofNat, hk0]
    · intro hk; simp [ofNat] at hk; subst hk; exact h
  · refine Or.inl ?_
    ext k
    constructor
    · intro hk
      obtain ⟨rfl, n, hn, hne⟩ := hk
      exact h ⟨rfl, n, hn, hne⟩
    · intro hk
      exact ((mem_botElem k).mp hk).elim

theorem closedToZero_three {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    ThreeValued (closedToZero C x) := by
  constructor
  by_cases hx : x ∈ C
  · refine Or.inr (Or.inl ?_)
    have : charTop Cᶜ x = botElem := (charTop_eq_bot_of_closed hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, botElem]
  · refine Or.inr (Or.inr ?_)
    have : charTop Cᶜ x = topElem := (charTop_eq_top hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, topElem]

theorem charOpen_eq_zero {U : Set Pomega} (hU : IsScottOpen U) (x : Pomega) :
    charOpen U x = ofNat 0 ↔ x ∈ U := by
  constructor
  · intro h
    have : 0 ∈ charOpen U x := by rw [h]; simp [ofNat]
    obtain ⟨_, n, hn, hne⟩ := this
    exact isScottOpen_isUpper hU hne hn
  · intro hx
    ext k
    constructor
    · intro ⟨hk0, _⟩; simp [ofNat, hk0]
    · intro hk
      simp [ofNat] at hk
      subst hk
      obtain ⟨n, hn, hne⟩ := (mem_isScottOpen_iff hU).mp hx
      exact ⟨rfl, n, hn, hne⟩

theorem closedToZero_eq_zero {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    closedToZero C x = ofNat 0 ↔ x ∈ C := by
  constructor
  · intro h
    by_contra hx
    have htop : charTop Cᶜ x = topElem := (charTop_eq_top hC x).mpr hx
    have : closedToZero C x = topElem := by
      ext k
      simp [closedToZero, htop]
    exact top_ne_ofNat_zero (this.symm.trans h)
  · intro hx
    have : charTop Cᶜ x = botElem := (charTop_eq_bot_of_closed hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, botElem]

theorem isScottOpen_not_subset {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (e : Pomega) : IsScottOpen {x | ¬ f x ⊆ e} := by
  have : {x | ¬ f x ⊆ e} = ⋃ k, {x | k ∉ e ∧ k ∈ f x} := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, hke⟩ := Set.not_subset.mp hx
      exact Set.mem_iUnion.mpr ⟨k, ⟨hke, hk⟩⟩
    · intro hx
      obtain ⟨k, hke, hk⟩ := Set.mem_iUnion.mp hx
      intro hsub
      exact hke (hsub hk)
  rw [this]
  exact isScottOpen_iUnion _ fun k => by
    by_cases hke : k ∈ e
    · have : {x | k ∉ e ∧ k ∈ f x} = (∅ : Set Pomega) := by
        ext x; simp [hke]
      rw [this]; exact isScottOpen_empty
    · have : {x | k ∉ e ∧ k ∈ f x} = {x | k ∈ f x} := by
        ext x; simp [hke]
      rw [this]; exact mem_preimage_isScottOpen hf k

theorem isScottOpen_subset_preimage {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {e : Pomega} (he : e.Finite) : IsScottOpen {x | e ⊆ f x} := by
  have : {x | e ⊆ f x} = ⋂ k ∈ he.toFinset, {x | k ∈ f x} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iInter₂.mpr fun k hk => hx (he.mem_toFinset.mp hk)
    · intro hx k hk
      exact Set.mem_iInter₂.mp hx k (he.mem_toFinset.mpr hk)
  rw [this, isScottOpen_iff_isOpen]
  exact isOpen_biInter_finset fun k _ =>
    (isScottOpen_iff_isOpen _).mp (mem_preimage_isScottOpen hf k)

theorem ne_eq_open_union_closed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {e : Pomega} (he : e.Finite) :
    {x | f x ≠ e} = {x | ¬ f x ⊆ e} ∪ {x | ¬ e ⊆ f x} ∧
      IsScottOpen {x | ¬ f x ⊆ e} ∧
      IsScottOpen {x | ¬ e ⊆ f x}ᶜ := by
  refine ⟨?_, isScottOpen_not_subset hf e, ?_⟩
  · ext x
    constructor
    · intro hne
      by_cases hsub : f x ⊆ e
      · refine Or.inr fun hsup => hne (subset_antisymm hsub hsup)
      · exact Or.inl hsub
    · intro h heq
      rcases h with h | h
      · exact h heq.subset
      · exact h heq.symm.subset
  · have : {x | ¬ e ⊆ f x}ᶜ = {x | e ⊆ f x} := by
      ext x; simp
    rw [this]
    exact isScottOpen_subset_preimage hf he

/-- Every Boolean set is a countable intersection of `(open ∪ closed)` sets,
    by writing the complement in the Theorem 6.6 form `{f ∈ E}` and taking
    De Morgan duals. Extra indices are padded by `univ ∪ ∅`. -/
theorem isBooleanOpen_as_iInter_open_union_closed {U : Set Pomega}
    (hU : IsBooleanOpen U) :
    ∃ (O C : ℕ → Set Pomega),
      (∀ n, IsScottOpen (O n)) ∧ (∀ n, IsScottOpen (C n)ᶜ) ∧
        U = ⋂ n, O n ∪ C n := by
  have hUc : Uᶜ ∈ ScottB := hU.compl
  obtain ⟨f, hf, E, hE, hEfin, hEeq⟩ := (theorem_6_6 Uᶜ).mp hUc
  have hrec : ∀ {S : Set Pomega} (hS : S.Finite),
      (∀ e ∈ S, e.Finite) →
      ∃ O C : ℕ → Set Pomega,
        (∀ n, IsScottOpen (O n)) ∧ (∀ n, IsScottOpen (C n)ᶜ) ∧
          {x | f x ∉ S} = ⋂ n, O n ∪ C n := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty =>
      intro
      refine ⟨fun _ => Set.univ, fun _ => ∅, fun _ => isScottOpen_univ,
        fun _ => by rw [Set.compl_empty]; exact isScottOpen_univ, ?_⟩
      ext x
      simp
    | insert ha hs ih =>
      intro hfin
      rename_i a s
      obtain ⟨Os, Cs, hOs, hCs, hseq⟩ :=
        ih fun e he => hfin e (Set.mem_insert_of_mem a he)
      have haFin : a.Finite := hfin a (Set.mem_insert a s)
      obtain ⟨hslice, hOa, hCa⟩ := ne_eq_open_union_closed hf haFin
      refine ⟨fun n => match n with
        | 0 => {x | ¬ f x ⊆ a}
        | _n + 1 => Os _n,
        fun n => match n with
        | 0 => {x | ¬ a ⊆ f x}
        | _n + 1 => Cs _n, ?_, ?_, ?_⟩
      · intro n
        cases n with
        | zero => exact hOa
        | succ n => exact hOs n
      · intro n
        cases n with
        | zero => exact hCa
        | succ n => exact hCs n
      · have hUeq : {x | f x ∉ insert a s} =
            ({x | f x ≠ a} ∩ {x | f x ∉ s}) := by
          ext x
          simp [Set.mem_insert_iff]
        rw [hUeq, hslice, hseq]
        ext x
        constructor
        · intro ⟨ha', hs'⟩
          refine Set.mem_iInter.mpr fun n => ?_
          cases n with
          | zero => exact ha'
          | succ n => exact Set.mem_iInter.mp hs' n
        · intro hx
          exact ⟨Set.mem_iInter.mp hx 0,
            Set.mem_iInter.mpr fun n => Set.mem_iInter.mp hx (n + 1)⟩
  obtain ⟨O, C, hO, hC, hOC⟩ := hrec hE hEfin
  refine ⟨O, C, hO, hC, ?_⟩
  have hUeq : U = {x | f x ∉ E} := by
    ext x
    constructor
    · intro hxU hfxE
      have hxUc : x ∈ Uᶜ := by
        rw [hEeq]
        exact hfxE
      exact hxUc hxU
    · intro hx
      by_contra hxU
      apply hx
      change x ∈ {x | f x ∈ E}
      rwa [← hEeq]
  rw [hUeq, hOC]

/-- **Scott 1976, Theorem 6.7, `B_δ` → equalizer.**
Each Boolean slice is a countable intersection of `(open ∪ closed)` sets;
each such union is `{fₙ = 0} ∪ {gₙ = 0}` with three-valued continuous `fₙ, gₙ`;
Scott's tables pack that union as an equalizer; `pairIndexed` packs the
countable intersection. -/
theorem theorem_6_7_of_bdelta {U : Set Pomega} (hU : IsBdelta U) :
    ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧ U = {x | f x = g x} := by
  obtain ⟨Bs, hB, rfl⟩ := hU
  have hslice : ∀ n, ∃ O C : ℕ → Set Pomega,
      (∀ k, IsScottOpen (O k)) ∧ (∀ k, IsScottOpen (C k)ᶜ) ∧
        Bs n = ⋂ k, O k ∪ C k :=
    fun n => isBooleanOpen_as_iInter_open_union_closed (hB n)
  choose Os Cs hOs hCs hEq using hslice
  let O (m : ℕ) : Set Pomega := Os (unpair m).1 (unpair m).2
  let C (m : ℕ) : Set Pomega := Cs (unpair m).1 (unpair m).2
  have hO : ∀ m, IsScottOpen (O m) := fun m => hOs (unpair m).1 (unpair m).2
  have hC : ∀ m, IsScottOpen (C m)ᶜ := fun m => hCs (unpair m).1 (unpair m).2
  have hUC : (⋂ n, Bs n) = ⋂ m, O m ∪ C m := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter.mpr fun m => ?_
      have hx' := Set.mem_iInter.mp hx (unpair m).1
      rw [hEq] at hx'
      exact Set.mem_iInter.mp hx' (unpair m).2
    · intro hx
      refine Set.mem_iInter.mpr fun n => ?_
      rw [hEq]
      refine Set.mem_iInter.mpr fun k => ?_
      simpa [O, C, unpair_pair] using Set.mem_iInter.mp hx (pair n k)
  let f : ℕ → Pomega → Pomega := fun m x => charOpen (O m) x
  let g : ℕ → Pomega → Pomega := fun m x => closedToZero (C m) x
  have hf : ∀ m, IsScottContinuous (f m) :=
    fun m => charOpen_isScottContinuous (O m)
  have hg : ∀ m, IsScottContinuous (g m) :=
    fun m => closedToZero_isScottContinuous (C m)
  let F : ℕ → Pomega → Pomega := fun m x => uvU (f m x) (g m x)
  let G : ℕ → Pomega → Pomega := fun m x => uvV (f m x) (g m x)
  have hF : ∀ m, IsScottContinuous (F m) :=
    fun m => theorem_1_3.tuple (uvU_isScottContinuous_left) (uvU_isScottContinuous_right)
      (hf m) (hg m)
  have hG : ∀ m, IsScottContinuous (G m) :=
    fun m => theorem_1_3.tuple (uvV_isScottContinuous_left) (uvV_isScottContinuous_right)
      (hf m) (hg m)
  have hpack : (⋂ n, Bs n) = {x | ∀ m, F m x = G m x} := by
    rw [hUC]
    ext x
    constructor
    · intro hx m
      have hx' := Set.mem_iInter.mp hx m
      have hfg : f m x = ofNat 0 ∨ g m x = ofNat 0 := by
        rcases hx' with hOm | hCm
        · exact Or.inl ((charOpen_eq_zero (hO m) x).mpr hOm)
        · exact Or.inr ((closedToZero_eq_zero (hC m) x).mpr hCm)
      exact (uv_eq_iff (charOpen_three (O m) x) (closedToZero_three (hC m) x)).mpr hfg
    · intro hx
      refine Set.mem_iInter.mpr fun m => ?_
      have heq := (uv_eq_iff (charOpen_three (O m) x)
        (closedToZero_three (hC m) x)).mp (hx m)
      rcases heq with hf0 | hg0
      · exact Or.inl ((charOpen_eq_zero (hO m) x).mp hf0)
      · exact Or.inr ((closedToZero_eq_zero (hC m) x).mp hg0)
  exact theorem_6_7_converse_of_equalizers F G hF hG hpack

/-- **Scott 1976, Theorem 6.7 (The 𝔅_δ theorem).**
The `B_δ` subsets of `Pω` are exactly the equalizers of pairs of continuous
maps. -/
theorem theorem_6_7 :
    ∀ U, IsBdelta U ↔
      ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
        U = {x | f x = g x} :=
  fun U => ⟨theorem_6_7_of_bdelta, theorem_6_7_of_equalizer U⟩

theorem seq2_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => seq2 x y) :=
  graph_const_isScottContinuous
    (fun x z => condSet z x (condSet (predSet z) y botElem))
    (fun z => condSet.isScottContinuous_mid z _)

theorem seq2_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => seq2 x y) :=
  graph_const_isScottContinuous
    (fun y z => condSet z x (condSet (predSet z) y botElem))
    (fun z =>
      theorem_1_3 (condSet.isScottContinuous_right z x)
        (condSet.isScottContinuous_mid (predSet z) botElem))

theorem seq2_pair_isScottContinuous {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun x => seq2 (f x) (g x)) :=
  theorem_1_3.tuple seq2_isScottContinuous_left seq2_isScottContinuous_right hf hg


/-- **Scott 1976, Table 3 / Theorem 6.7.** `𝔅_δ` is the class of continuous
preimages of `{u | u₀ = u₁}`. -/
theorem typicalBdelta_universal (U : Set Pomega) :
    IsBdelta U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalBdelta} := by
  constructor
  · intro hU
    obtain ⟨F, G, hF, hG, rfl⟩ := (theorem_6_7 U).mp hU
    refine ⟨fun x => seq2 (F x) (G x), seq2_pair_isScottContinuous hF hG, ?_⟩
    ext x
    constructor
    · intro h
      change funOf (seq2 (F x) (G x)) (ofNat 0) =
        funOf (seq2 (F x) (G x)) (ofNat 1)
      rw [seq2_app_zero, seq2_app_one]
      exact h
    · intro h
      have : funOf (seq2 (F x) (G x)) (ofNat 0) =
          funOf (seq2 (F x) (G x)) (ofNat 1) := h
      rw [seq2_app_zero, seq2_app_one] at this
      exact this
  · rintro ⟨f, hf, rfl⟩
    exact (theorem_6_7 _).mpr
      ⟨fun x => funOf (f x) (ofNat 0), fun x => funOf (f x) (ofNat 1),
        theorem_1_3 (f := fun u => funOf u (ofNat 0))
          (funOf_isScottContinuous_left (ofNat 0)) hf,
        theorem_1_3 (f := fun u => funOf u (ofNat 1))
          (funOf_isScottContinuous_left (ofNat 1)) hf, rfl⟩
end DomainTheory.DataTypesAsLattices
