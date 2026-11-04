module

public import DomainTheory.DataTypesAsLattices.Classification.ThreeValued
import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous
import DomainTheory.DataTypesAsLattices.Continuous.IsScottOpen_more
import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_isUpper
import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.ofNat_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def charOpen (U : Set Pomega) (x : Pomega) : Pomega :=
  {k | k = 0 ∧ ∃ n, e n ⊆ x ∧ e n ∈ U}

namespace charOpen

theorem isScottContinuous (U : Set Pomega) :
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

theorem eq_zero {U : Set Pomega} (hU : IsScottOpen U) (x : Pomega) :
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
      obtain ⟨n, hn, hne⟩ := (IsScottOpen.mem_iff hU).mp hx
      exact ⟨rfl, n, hn, hne⟩

theorem threeValued (U : Set Pomega) (x : Pomega) :
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

end charOpen

def charTop (U : Set Pomega) (x : Pomega) : Pomega :=
  {_k | ∃ n, e n ⊆ x ∧ e n ∈ U}

namespace charTop

theorem isScottContinuous (U : Set Pomega) :
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

theorem eq_top {U : Set Pomega} (hU : IsScottOpen U) (x : Pomega) :
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
      exact (IsScottOpen.mem_iff hU).mp hx

theorem eq_bot {U : Set Pomega} (hU : IsScottOpen U) (x : Pomega) :
    charTop U x = botElem ↔ x ∉ U := by
  constructor
  · intro h hx
    have : charTop U x = topElem := (eq_top hU x).mpr hx
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

theorem eq_bot_of_closed {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    charTop Cᶜ x = botElem ↔ x ∈ C := by
  rw [eq_bot hC]
  simp

end charTop

def closedToZero (C : Set Pomega) (x : Pomega) : Pomega :=
  ofNat 0 ∪ charTop Cᶜ x

namespace closedToZero

theorem isScottContinuous (C : Set Pomega) :
    IsScottContinuous (closedToZero C) :=
  theorem_1_3.tuple (f := fun a b => (a ∪ b : Pomega))
    union_left_isScottContinuous
    (fun x => by
      convert union_left_isScottContinuous x using 1
      funext y; exact (Set.union_comm y x).symm)
    (const_isScottContinuous (ofNat 0)) (charTop.isScottContinuous Cᶜ)

theorem threeValued {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    ThreeValued (closedToZero C x) := by
  constructor
  by_cases hx : x ∈ C
  · refine Or.inr (Or.inl ?_)
    have : charTop Cᶜ x = botElem := (charTop.eq_bot_of_closed hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, botElem]
  · refine Or.inr (Or.inr ?_)
    have : charTop Cᶜ x = topElem := (charTop.eq_top hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, topElem]

theorem eq_zero {C : Set Pomega} (hC : IsScottOpen Cᶜ) (x : Pomega) :
    closedToZero C x = ofNat 0 ↔ x ∈ C := by
  constructor
  · intro h
    by_contra hx
    have htop : charTop Cᶜ x = topElem := (charTop.eq_top hC x).mpr hx
    have : closedToZero C x = topElem := by
      ext k
      simp [closedToZero, htop]
    exact topElem.ne_ofNat_zero (this.symm.trans h)
  · intro hx
    have : charTop Cᶜ x = botElem := (charTop.eq_bot_of_closed hC x).mpr hx
    ext k
    simp [closedToZero, this, ofNat, botElem]

end closedToZero

end DomainTheory.DataTypesAsLattices
