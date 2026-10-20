/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem74
public import DomainTheory.Neighborhood.Exercise510
public import DomainTheory.Neighborhood.Exercise316
public import DomainTheory.Neighborhood.Exercise715.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}







variable (P₀ P₁)














/-- **The smash projection `p₀` is computable.** `(smashEnum n) p₀ X⁰_m ↔ X⁰_{effL n} ⊆ X⁰_m`
(`smashEnum_eq_eff` rewrites `Sum.inl ⁻¹' (smashEnum n)` to the effective left factor), a recursive
slice of `incl_computable`. -/
theorem smashProj₀_isComputable :
    IsComputableMapS (smashPresentation P₀ P₁) P₀.toScott (smashProj₀ V₀ V₁) := by
  obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
  obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
  set c₀ := fun n => isOne (f₀ n) with hc₀def
  set c₁ := fun n => isOne (f₁ n) with hc₁def
  have hc₀le : ∀ n, c₀ n ≤ 1 := fun n => isOne_le_one _
  have hc₁le : ∀ n, c₁ n ≤ 1 := fun n => isOne_le_one _
  have hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1 := fun n => by
    rw [hc₀def, isOne_eq_one_iff]; exact hf₀e n
  have hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1 := fun n => by
    rw [hc₁def, isOne_eq_one_iff]; exact hf₁e n
  have hc₀p : Nat.Primrec c₀ := primrec_isOne.comp hf₀p
  have hc₁p : Nat.Primrec c₁ := primrec_isOne.comp hf₁p
  have hpf : Nat.Primrec (fun n => c₀ n.unpair.1 * c₁ n.unpair.2) :=
    (primrec_mul.comp ((hc₀p.comp Nat.Primrec.left).pair (hc₁p.comp Nat.Primrec.right))).of_eq
      (fun n => by simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd])
  have heffLp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.1 P₀.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.left (Nat.Primrec.const _)
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2) t.unpair.1.unpair.1 P₀.masterIdx)
      t.unpair.2) := (heffLp.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  show (smashProj₀ V₀ V₁).rel (smashEnum P₀ P₁ t.unpair.1) (P₀.X t.unpair.2) ↔ _
  simp only [smashProj₀_rel, unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨-, -, hsub⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, inl_preimage_prodNbhd] at hsub
    exact hsub
  · intro h
    refine ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) _, P₀.mem_X _, ?_⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, inl_preimage_prodNbhd]
    exact h

end Smash
end DomainTheory.Neighborhood
