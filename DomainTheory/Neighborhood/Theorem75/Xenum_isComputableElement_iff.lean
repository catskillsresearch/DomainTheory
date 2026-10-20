/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.Theorem74
public import DomainTheory.Neighborhood.Theorem75.Basic
public import DomainTheory.Neighborhood.Theorem75.mem_Xenum_iff

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)








































































































/-- **Theorem 7.5 (Scott 1981, PRG-19) — computable elements = computable maps (choice-free).** For
the function-space enumeration `Xenum` built from a consistency char `gN`, an element `φ` has an r.e.
index set iff the corresponding approximable map `toApproxMap φ` is computable. -/
theorem Xenum_isComputableElement_iff (gN : ℕ → ℕ) (hgNp : Nat.Primrec gN)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (φ : (funSpace V₀ V₁).Element) :
    REPred (fun c => φ.mem (Xenum P₀ P₁ gN c)) ↔ IsComputableMap P₀ P₁ (toApproxMap φ) := by
  -- `IsComputableMap` unfolds (def-eq) to r.e.-ness of `R' s = φ ∋ [X₀_{s.1}, X₁_{s.2}]`.
  have hbridge := mem_Xenum_iff P₀ P₁ gN φ
  constructor
  · -- element computable ⟹ map computable: reindex by the single-step code `pair s 0 + 1`.
    intro helem
    have hc0p : Nat.Primrec (fun s => Nat.pair s 0 + 1) :=
      Nat.Primrec.succ.comp (primrec_id.pair (Nat.Primrec.const 0))
    have key : REPred (fun s => φ.mem (Xenum P₀ P₁ gN (Nat.pair s 0 + 1))) := helem.comp hc0p
    show REPred (fun s => φ.mem (step (P₀.X s.unpair.1) (P₁.X s.unpair.2)))
    refine REPred.of_iff (fun s => ?_) key
    have hdec : decodeList (Nat.pair s 0 + 1) = [s] := by
      rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
    have hcons : gN (Nat.pair s 0 + 1) = 1 := by
      rw [hgN, hdec]
      show (stepFun [(P₀.X s.unpair.1, P₁.X s.unpair.2)]
        : Set (ApproximableMap V₀ V₁)).Nonempty
      rw [stepFun_singleton]
      exact (step_mem (P₀.mem_X _) (P₁.mem_X _)).2
    rw [hbridge (Nat.pair s 0 + 1), hdec]
    constructor
    · intro hRs _ e he; rw [List.mem_singleton] at he; subst he; exact hRs
    · intro h; exact h hcons s (List.mem_singleton.mpr rfl)
  · -- map computable ⟹ element computable: guard the bounded-`∀` by the decidable `gN c = 1`.
    intro hmap
    have hR' : REPred (fun s => φ.mem (step (P₀.X s.unpair.1) (P₁.X s.unpair.2))) := hmap
    have hforall : REPred (fun c => ∀ e ∈ decodeList c,
        φ.mem (step (P₀.X e.unpair.1) (P₁.X e.unpair.2))) := hR'.forall_mem_decodeList
    have hne1 : REPred (fun c => ¬ gN c = 1) :=
      ((RecDecidable.natEq hgNp (Nat.Primrec.const 1)).not).re
    refine REPred.of_iff (fun c => ?_) (hne1.or hforall)
    rw [hbridge c]; exact Decidable.imp_iff_not_or

end DomainTheory.Neighborhood
