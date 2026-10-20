/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap_rel_fin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.gather_witnesses

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}






/-- **Choice-free witness gathering (list of step constraints).** From a finite list `L` of
`ℙD × ℙE`-neighbourhood pairs `(A, B)`, each satisfied by `ℙf` (`(ℙf).rel A B`), build a *single*
finite list `M` of `D × E`-pairs, `f`-related and covering every generator of every `A` in `L`, such
that *any* `g` agreeing with `f` on `M` again satisfies `(ℙg).rel A B` for every `(A, B) ∈ L`. This is
exactly "continuity of `f ↦ ℙf`, unwound to finite data": `M` is the finite portion of `f` that
already forces `ℙf`'s membership in every step-neighbourhood of `L`. -/
theorem exists_stepFun_forall_PFmap_rel (f : ApproximableMap V W) :
    ∀ (L : List (Set (Set α) × Set (Set β))),
      (∀ p ∈ L, V.PDmem p.1 ∧ W.PDmem p.2) → (∀ p ∈ L, (PFmap f).rel p.1 p.2) →
      ∃ M : List (Set α × Set β), (∀ p ∈ M, V.mem p.1 ∧ W.mem p.2) ∧
        (∀ p ∈ M, f.rel p.1 p.2) ∧
        ∀ g : ApproximableMap V W, (∀ p ∈ M, g.rel p.1 p.2) → ∀ p ∈ L, (PFmap g).rel p.1 p.2 := by
  intro L
  induction L with
  | nil => intro _ _; exact ⟨[], by simp, by simp, by simp⟩
  | cons p L ih =>
    intro hL hf
    obtain ⟨hA, hB⟩ := hL p (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨L₁, hL₁, hAeq⟩ := hA
    obtain ⟨L₂, hL₂, hBeq⟩ := hB
    have hrelAB : (PFmap f).rel p.1 p.2 := hf p (List.mem_cons.mpr (Or.inl rfl))
    rw [hAeq, hBeq] at hrelAB
    have hgen := (PFmap_rel_fin f hL₁ hL₂).mp hrelAB
    obtain ⟨M₀, hM₀prop, hM₀wit⟩ := gather_witnesses f L₁ L₂ hgen
    obtain ⟨M, hMmem, hMrel, hMgen⟩ :=
      ih (fun p' hp' => hL p' (List.mem_cons.mpr (Or.inr hp')))
         (fun p' hp' => hf p' (List.mem_cons.mpr (Or.inr hp')))
    refine ⟨M₀ ++ M, ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq' | hq'
      · obtain ⟨hq1, hq2, _⟩ := hM₀prop q hq'
        exact ⟨hL₁ q.1 hq1, hL₂ q.2 hq2⟩
      · exact hMmem q hq'
    · intro q hq
      rcases List.mem_append.mp hq with hq' | hq'
      · exact (hM₀prop q hq').2.2
      · exact hMrel q hq'
    · intro g hg p' hp'
      rcases List.mem_cons.mp hp' with rfl | hp''
      · rw [hAeq, hBeq]
        refine (PFmap_rel_fin g hL₁ hL₂).mpr ?_
        intro X hX
        obtain ⟨Y, hY, hmem⟩ := hM₀wit X hX
        exact ⟨Y, hY, hg (X, Y) (List.mem_append.mpr (Or.inl hmem))⟩
      · exact hMgen g (fun q hq => hg q (List.mem_append.mpr (Or.inr hq))) p' hp''

end DomainTheory.NeighbourhoodSystems
