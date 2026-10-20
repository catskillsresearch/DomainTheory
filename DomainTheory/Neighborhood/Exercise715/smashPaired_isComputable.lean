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














/-- **The strict pairing `⟨a, b⟩⊗` is computable.** `Zₙ ⟨a,b⟩⊗ (smashEnum m) ↔` either `m` improper
(the codomain master absorbs) or `m` proper together with `a`'s and `b`'s r.e. relations on the
(raw) codomain coordinate indices — an `∨`/`∧` of r.e. predicates and the codomain properness tests.
No effective-index bridge is needed: the proper branch reads `smashEnum`'s raw factors directly. -/
theorem smashPaired_isComputable {V₂ : NeighborhoodSystem γ} (P₂ : ComputablePresentation V₂)
    {a : ApproximableMap V₂ V₀} {b : ApproximableMap V₂ V₁}
    (ha : IsComputableMapS P₂.toScott P₀.toScott a)
    (hb : IsComputableMapS P₂.toScott P₁.toScott b) :
    IsComputableMapS P₂.toScott (smashPresentation P₀ P₁) (smashPaired a b) := by
  have Ha : REPred (fun t => a.rel (P₂.toScott.X t.unpair.1) (P₀.toScott.X t.unpair.2.unpair.1)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (ha.comp (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right)))
  have Hb : REPred (fun t => b.rel (P₂.toScott.X t.unpair.1) (P₁.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hb.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hJP : RecDecidable (fun t => P₀.X t.unpair.2.unpair.1 ≠ V₀.master ∧
      P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
    ((proper₀_dec P₀).comp (Nat.Primrec.left.comp Nat.Primrec.right)).and
      ((proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right))
  refine REPred.of_iff (fun t => ?_) ((hJP.not.re).or (hJP.re.and (Ha.and Hb)))
  show (smashPaired a b).rel (P₂.X t.unpair.1) (smashEnum P₀ P₁ t.unpair.2) ↔ _
  by_cases hJPm : P₀.X t.unpair.2.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
  · constructor
    · rintro ⟨-, -, hd⟩
      rcases hd with hmaster | ⟨A, B, hWAB, -, -, ha', hb'⟩
      · rw [smashEnum_proper hJPm] at hmaster
        exact absurd (prodNbhd_injective hmaster).1 hJPm.1
      · rw [smashEnum_proper hJPm] at hWAB
        obtain ⟨rfl, rfl⟩ := prodNbhd_injective hWAB
        exact Or.inr ⟨hJPm, ha', hb'⟩
    · rintro (hnp | ⟨-, ha', hb'⟩)
      · exact absurd hJPm hnp
      · exact ⟨P₂.mem_X _, smashEnum_mem (P₀ := P₀) (P₁ := P₁) _,
          Or.inr ⟨_, _, smashEnum_proper hJPm, hJPm.1, hJPm.2, ha', hb'⟩⟩
  · constructor
    · intro _; exact Or.inl hJPm
    · intro _
      exact ⟨P₂.mem_X _, smashEnum_mem (P₀ := P₀) (P₁ := P₁) _,
        Or.inl (smashEnum_master hJPm)⟩

end Smash
end DomainTheory.Neighborhood
