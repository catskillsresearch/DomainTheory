/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
import all Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
import all Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import all Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.not_isCompactElt_pos

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap










































/-- **Exercise 8.11 (conclusion).** `a` is *not* finitary: were it, its fixed-point set — order
isomorphic to `Set.Icc (0:ℝ) 1` via `fixOrderIso` — would also be order isomorphic to some `F.Element`,
which is algebraic (`eq_iSupDirected_principal`); but every principal approximant of `g ⟨1,_,_⟩`
would then be compact, hence (`not_isCompactElt_pos`) equal to `g ⟨0,_,_⟩`, forcing
`g ⟨1,_,_⟩ = g ⟨0,_,_⟩` — contradicting injectivity of `g` at `1 ≠ 0`. Exactly Scott's hint: aside
from `⊥`, `{x ∣ x = a(x)}` has no finite elements, so it cannot be algebraic unless it is trivial. -/
theorem not_isFinitary_a : ¬ IsFinitary a := by
  rintro ⟨β, F, ⟨e⟩⟩
  set g : Set.Icc (0 : ℝ) 1 ≃o F.Element := fixOrderIso.symm.trans e with hgdef
  set x : F.Element := g ⟨1, zero_le_one, le_refl 1⟩ with hxdef
  have hcompact_bot : ∀ i : {X : Set β // x.mem X}, F.principal (x.sub i.2) = g ⟨0, le_refl 0, zero_le_one⟩ := by
    intro i
    by_contra hne
    have hc0 : g.symm (F.principal (x.sub i.2)) ≠ ⟨0, le_refl 0, zero_le_one⟩ := fun h => hne (by
      rw [← h, OrderIso.apply_symm_apply])
    have ht0 : (0:ℝ) ≤ (g.symm (F.principal (x.sub i.2))).1 := (g.symm (F.principal (x.sub i.2))).2.1
    have ht1 : (g.symm (F.principal (x.sub i.2))).1 ≤ 1 := (g.symm (F.principal (x.sub i.2))).2.2
    have htpos : 0 < (g.symm (F.principal (x.sub i.2))).1 := by
      rcases ht0.lt_or_eq with h | h
      · exact h
      · exact absurd (Subtype.ext h.symm) hc0
    have hsub : (⟨(g.symm (F.principal (x.sub i.2))).1, ht0, ht1⟩ : Set.Icc (0 : ℝ) 1)
        = g.symm (F.principal (x.sub i.2)) := Subtype.ext rfl
    have heq2 : F.principal (x.sub i.2) = g ⟨(g.symm (F.principal (x.sub i.2))).1, ht0, ht1⟩ := by
      rw [hsub, OrderIso.apply_symm_apply]
    exact not_isCompactElt_pos g ht0 ht1 htpos (heq2 ▸ principal_isCompactElt (x.sub i.2))
  have hxeq : x = g ⟨0, le_refl 0, zero_le_one⟩ := by
    conv_lhs => rw [eq_iSupDirected_principal x]
    apply le_antisymm
    · apply iSupDirected_le
      intro i
      exact le_of_eq (hcompact_bot i)
    · obtain ⟨i0⟩ := (instNonemptyMemSubtype x)
      have hstep : g ⟨0, le_refl 0, zero_le_one⟩ ≤
          iSupDirected (fun j : {X : Set β // x.mem X} => F.principal (x.sub j.2))
            (principalFamily_directed x) := by
        rw [← hcompact_bot i0]
        exact le_iSupDirected (fun j : {X : Set β // x.mem X} => F.principal (x.sub j.2))
          (principalFamily_directed x) i0
      exact hstep
  have : (⟨1, zero_le_one, le_refl 1⟩ : Set.Icc (0:ℝ) 1) = ⟨0, le_refl 0, zero_le_one⟩ :=
    g.injective hxeq
  exact absurd (congrArg Subtype.val this) one_ne_zero

end DomainTheory.NeighbourhoodSystems.Exercise811
