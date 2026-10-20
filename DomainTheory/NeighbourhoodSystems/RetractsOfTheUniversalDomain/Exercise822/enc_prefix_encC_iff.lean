/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_prefix_of_prefix

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- **The marker never collides with a real prefix.** `enc ρ <+: encC σ` exactly reproduces `C`'s
own "cone ⊆ completed" relation `ρ <+: σ`: the extra length used by the marker can never be
matched by a genuine (doubled) continuation, since `[b, b] ≠ [true, false]`. -/
theorem enc_prefix_encC_iff {ρ σ : Str} : enc ρ <+: encC σ ↔ ρ <+: σ := by
  constructor
  · induction ρ generalizing σ with
    | nil => intro _; exact List.nil_prefix
    | cons b ρ' ih =>
      intro h
      cases σ with
      | nil =>
        exfalso
        rw [enc_cons, encC_nil] at h
        obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
        obtain ⟨h3, -⟩ := List.cons_prefix_cons.mp h2
        exact absurd h3 (by decide)
      | cons c σ' =>
        rw [enc_cons, encC_cons] at h
        obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
        obtain ⟨-, h3⟩ := List.cons_prefix_cons.mp h2
        rw [List.cons_prefix_cons]
        exact ⟨rfl, ih h3⟩
  · intro h
    calc enc ρ <+: enc σ := enc_prefix_of_prefix h
      _ <+: encC σ := ⟨[true, false], rfl⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
