module

public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_6
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

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

theorem theorem_6_7_converse_of_equalizers (f g : ℕ → Pomega → Pomega)
    (hf : ∀ n, IsScottContinuous (f n)) (hg : ∀ n, IsScottContinuous (g n))
    {U : Set Pomega} (hU : U = {x | ∀ n, f n x = g n x}) :
    ∃ F G, IsScottContinuous F ∧ IsScottContinuous G ∧ U = {x | F x = G x} := by
  obtain ⟨F, G, hF, hG, h⟩ := theorem_6_7_iInter_equalizer f g hf hg
  exact ⟨F, G, hF, hG, hU.trans h⟩

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
      rw [seq2.zero, seq2.one]
      exact h
    · intro h
      have : funOf (seq2 (F x) (G x)) (ofNat 0) =
          funOf (seq2 (F x) (G x)) (ofNat 1) := h
      rw [seq2.zero, seq2.one] at this
      exact this
  · rintro ⟨f, hf, rfl⟩
    exact (theorem_6_7 _).mpr
      ⟨fun x => funOf (f x) (ofNat 0), fun x => funOf (f x) (ofNat 1),
        theorem_1_3 (f := fun u => funOf u (ofNat 0))
          (funOf.isScottContinuous_left (ofNat 0)) hf,
        theorem_1_3 (f := fun u => funOf u (ofNat 1))
          (funOf.isScottContinuous_left (ofNat 1)) hf, rfl⟩

end DomainTheory.DataTypesAsLattices
