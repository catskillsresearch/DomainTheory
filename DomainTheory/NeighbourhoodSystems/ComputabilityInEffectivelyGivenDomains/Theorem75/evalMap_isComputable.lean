/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_singleton
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.evalMap_rel_prodNbhd_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)









































































































/-- **Theorem 7.5 (Scott 1981, PRG-19) — `eval` is computable (choice-free).** Relative to the
function-space presentation `funPresentation` (and the product/codomain presentations), the
evaluation map `eval : (𝒟₀ → 𝒟₁) × 𝒟₀ → 𝒟₁` is computable: its neighbourhood relation is the
*recursively decidable* function-space inclusion `Xenum c ⊆ [X₀ⱼ, Y₁ₘ]`, hence recursively
enumerable. -/
theorem evalMap_isComputable (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    IsComputableMap
      (prodPresentation (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
        hincl1 hincl1p heq1 heq1p) P₀) P₁ (evalMap V₀ V₁) := by
  -- The function-space inclusion is recursively decidable (`funPresentation.incl_computable`);
  -- `funPresentation.X` is definitionally `Xenum`, so we read it off directly.
  have hsub : RecDecidable (fun s => Xenum P₀ P₁ gN s.unpair.1 ⊆ Xenum P₀ P₁ gN s.unpair.2) :=
    (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
      hincl1 hincl1p heq1 heq1p).incl_computable
  -- Re-index `t ↦ ⟨(t.1).1, ⟨⟨(t.1).2, t.2⟩, 0⟩ + 1⟩`: `Xenum_{(t.1).1} ⊆ [X₀_{(t.1).2}, Y₁_{t.2}]`.
  have h11 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have h12 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hg : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1
      (Nat.pair (Nat.pair t.unpair.1.unpair.2 t.unpair.2) 0 + 1)) :=
    h11.pair (Nat.Primrec.succ.comp ((h12.pair Nat.Primrec.right).pair (Nat.Primrec.const 0)))
  refine (RecDecidable.of_iff (fun t => ?_) (hsub.comp hg)).re
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [Xenum_singleton P₀ P₁ gN hgN t.unpair.1.unpair.2 t.unpair.2,
    show (prodPresentation (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
        hincl1 hincl1p heq1 heq1p) P₀).X t.unpair.1
      = prodNbhd (Xenum P₀ P₁ gN t.unpair.1.unpair.1) (P₀.X t.unpair.1.unpair.2) from rfl,
    evalMap_rel_prodNbhd_iff (Xenum_mem P₀ P₁ gN hgN _) (P₀.mem_X _) (P₁.mem_X _)]

end DomainTheory.NeighbourhoodSystems
