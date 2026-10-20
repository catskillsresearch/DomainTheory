/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise319Sum

@[expose] public section

/-!
# Exercise 3.26, continued (Scott 1981, PRG-19, §3) — the sum-valued conditional and `which`

This module completes Exercise 3.26 with the two follow-up operators Scott asks for:

* the **sum-valued conditional** `condSum : T × D₀ × D₁ → D₀ + D₁`, routing `true → in₀`,
  `false → in₁`, `⊥ → ⊥`. It is obtained for free by *composition*: feeding the two inputs through
  the injections `in₀, in₁` into the common domain `S = D₀ + D₁` and then applying the conditional
  `cond S : T × S × S → S` of Exercise 3.26. The three identities follow from `cond_true/false/bot`.

* the discriminator **`which : D₀ + D₁ → T`** reading the tag (`0X ↦ true`, `1Y ↦ false`,
  `Λ ↦ ⊥`), together with Scott's identity

  `cond(which x, in₀(out₀ x), in₁(out₁ x)) = x`   for all `x ∈ |D₀ + D₁|`.

The discriminator is built directly as a neighbourhood relation; its three guards on the truth
component are mutually exclusive because the three forms of a sum-neighbourhood (`Λ`-master, left
copy, right copy) are mutually exclusive (Exercise 3.18, using non-emptiness).
-/

namespace DomainTheory.Neighborhood.Exercise326

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-! ### The sum-valued conditional `condSum`. -/

/-- The embedding `T × D₀ × D₁ → T × S × S` (`S = D₀ + D₁`) that injects the two value slots into
the sum via `in₀` and `in₁`, leaving the truth slot fixed. -/
def condSumEmb (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (prod TD (prod V₀ V₁)) (prod TD (prod (sum V₀ V₁ h₀ h₁) (sum V₀ V₁ h₀ h₁))) :=
  paired (proj₀ TD (prod V₀ V₁))
    (paired ((inMap₀ (h₀ := h₀) (h₁ := h₁)).comp ((proj₀ V₀ V₁).comp (proj₁ TD (prod V₀ V₁))))
      ((inMap₁ (h₀ := h₀) (h₁ := h₁)).comp ((proj₁ V₀ V₁).comp (proj₁ TD (prod V₀ V₁)))))

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The sum-valued conditional `T × D₀ × D₁ → D₀ + D₁`. -/
def condSum (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (prod TD (prod V₀ V₁)) (sum V₀ V₁ h₀ h₁) :=
  (cond (sum V₀ V₁ h₀ h₁)).comp (condSumEmb V₀ V₁ h₀ h₁)

/-! ### The discriminator `which : D₀ + D₁ → T`. -/

/-- A `T`-neighbourhood containing `Δ` is `Δ`. -/
theorem Tmem_ge_master {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.master ⊆ C) : C = Example12.master :=
  Set.Subset.antisymm (Example12.neighborhoodSystem.sub_master hC) h

/-- A `T`-neighbourhood containing `{0}` is `{0}` or `Δ`. -/
theorem Tmem_ge_zero {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.zero ⊆ C) : C = Example12.zero ∨ C = Example12.master := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact absurd (h (by simp [Example12.zero] : (0 : Example12.Token) ∈ Example12.zero))
      (by simp [Example12.one])

/-- A `T`-neighbourhood containing `{1}` is `{1}` or `Δ`. -/
theorem Tmem_ge_one {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.one ⊆ C) : C = Example12.one ∨ C = Example12.master := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact absurd (h (by simp [Example12.one] : (1 : Example12.Token) ∈ Example12.one))
      (by simp [Example12.zero])
  · exact Or.inl rfl

theorem inter_in_zeroset {C C' : Set Example12.Token} (hc : C = Example12.master ∨ C = Example12.zero)
    (hc' : C' = Example12.master ∨ C' = Example12.zero) :
    C ∩ C' = Example12.master ∨ C ∩ C' = Example12.zero := by
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl (Set.inter_self _)
  · exact Or.inr (Set.univ_inter _)
  · exact Or.inr (Set.inter_univ _)
  · exact Or.inr (Set.inter_self _)

theorem inter_in_oneset {C C' : Set Example12.Token} (hc : C = Example12.master ∨ C = Example12.one)
    (hc' : C' = Example12.master ∨ C' = Example12.one) :
    C ∩ C' = Example12.master ∨ C ∩ C' = Example12.one := by
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl (Set.inter_self _)
  · exact Or.inr (Set.univ_inter _)
  · exact Or.inr (Set.inter_univ _)
  · exact Or.inr (Set.inter_self _)

/-- Scott's guard for `which`: the truth output is `true` (`{0}`/`Δ`) on a left copy `0X`, `false`
(`{1}`/`Δ`) on a right copy `1Y`, and `⊥` (`Δ`) on the basepoint master. -/
def whichGuard (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (W : Set (Option (α ⊕ β))) (C : Set Example12.Token) : Prop :=
  ((∃ X, V₀.mem X ∧ W = inj₀ X) ∧ (C = Example12.master ∨ C = Example12.zero)) ∨
  ((∃ Y, V₁.mem Y ∧ W = inj₁ Y) ∧ (C = Example12.master ∨ C = Example12.one)) ∨
  (W = sumMaster V₀ V₁ ∧ C = Example12.master)

theorem whichGuard_left {W : Set (Option (α ⊕ β))} {C : Set Example12.Token} {X : Set α}
    (hg : whichGuard V₀ V₁ W C) (hW : W = inj₀ X) (hX : X.Nonempty) :
    C = Example12.master ∨ C = Example12.zero := by
  rcases hg with ⟨_, hc⟩ | ⟨⟨Y, _, hWY⟩, _⟩ | ⟨hWsm, _⟩
  · exact hc
  · refine absurd (hW.symm.trans hWY) ?_
    intro h; exact not_inj₀_subset_inj₁ hX h.subset
  · refine absurd (hW.symm.trans hWsm) ?_
    intro h; exact none_mem_inj₀ (h ▸ none_mem_sumMaster)

theorem whichGuard_right {W : Set (Option (α ⊕ β))} {C : Set Example12.Token} {Y : Set β}
    (hg : whichGuard V₀ V₁ W C) (hW : W = inj₁ Y) (hY : Y.Nonempty) :
    C = Example12.master ∨ C = Example12.one := by
  rcases hg with ⟨⟨X, _, hWX⟩, _⟩ | ⟨_, hc⟩ | ⟨hWsm, _⟩
  · refine absurd (hW.symm.trans hWX) ?_
    intro h; exact not_inj₁_subset_inj₀ hY h.subset
  · exact hc
  · refine absurd (hW.symm.trans hWsm) ?_
    intro h; exact none_mem_inj₁ (h ▸ none_mem_sumMaster)

theorem whichGuard_masterC {W : Set (Option (α ⊕ β))} {C : Set Example12.Token}
    (hg : whichGuard V₀ V₁ W C) (hW : W = sumMaster V₀ V₁) : C = Example12.master := by
  rcases hg with ⟨⟨X, _, hWX⟩, _⟩ | ⟨⟨Y, _, hWY⟩, _⟩ | ⟨_, hc⟩
  · refine absurd (hW.symm.trans hWX) ?_
    intro h; exact none_mem_inj₀ (h ▸ none_mem_sumMaster)
  · refine absurd (hW.symm.trans hWY) ?_
    intro h; exact none_mem_inj₁ (h ▸ none_mem_sumMaster)
  · exact hc

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The discriminator `which : D₀ + D₁ → T`. -/
def whichMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (sum V₀ V₁ h₀ h₁) TD where
  rel W C := (sum V₀ V₁ h₀ h₁).mem W ∧ Example12.mem C ∧ whichGuard V₀ V₁ W C
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, Example12.mem_master, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  inter_right := by
    rintro W C C' ⟨hW, _, hg⟩ ⟨_, _, hg'⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, hc⟩ | ⟨⟨Y, hY, rfl⟩, hc⟩ | ⟨rfl, hc⟩
    · have hor := inter_in_zeroset hc (whichGuard_left hg' rfl (h₀ X hX))
      refine ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), ?_, Or.inl ⟨⟨X, hX, rfl⟩, hor⟩⟩
      rcases hor with h | h
      · rw [h]; exact Example12.mem_master
      · rw [h]; exact Example12.mem_zero
    · have hor := inter_in_oneset hc (whichGuard_right hg' rfl (h₁ Y hY))
      refine ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), ?_, Or.inr (Or.inl ⟨⟨Y, hY, rfl⟩, hor⟩)⟩
      rcases hor with h | h
      · rw [h]; exact Example12.mem_master
      · rw [h]; exact Example12.mem_one
    · have hc' := whichGuard_masterC hg' rfl
      subst hc; subst hc'
      rw [Set.inter_self]
      exact ⟨Or.inl rfl, Example12.mem_master, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  mono := by
    rintro W W₂ C C₂ ⟨hW, hC, hg⟩ hW₂W hCC₂ hW₂ hC₂
    refine ⟨hW₂, hC₂, ?_⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, hc⟩ | ⟨⟨Y, hY, rfl⟩, hc⟩ | ⟨rfl, hc⟩
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂ hW₂W
      refine Or.inl ⟨⟨X₂, hX₂, rfl⟩, ?_⟩
      rcases hc with rfl | rfl
      · exact Or.inl (Tmem_ge_master hC₂ hCC₂)
      · exact Or.symm (Tmem_ge_zero hC₂ hCC₂)
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂ hW₂W
      refine Or.inr (Or.inl ⟨⟨Y₂, hY₂, rfl⟩, ?_⟩)
      rcases hc with rfl | rfl
      · exact Or.inl (Tmem_ge_master hC₂ hCC₂)
      · exact Or.symm (Tmem_ge_one hC₂ hCC₂)
    · subst hc
      have hC₂m : C₂ = Example12.master := Tmem_ge_master hC₂ hCC₂
      rcases hW₂ with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
      · exact Or.inr (Or.inr ⟨rfl, hC₂m⟩)
      · exact Or.inl ⟨⟨X₂, hX₂, rfl⟩, Or.inl hC₂m⟩
      · exact Or.inr (Or.inl ⟨⟨Y₂, hY₂, rfl⟩, Or.inl hC₂m⟩)

/-! ### Membership facts and the composite identity. -/
end DomainTheory.Neighborhood.Exercise326
