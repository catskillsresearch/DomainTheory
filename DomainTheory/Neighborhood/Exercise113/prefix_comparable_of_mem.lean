/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.ExampleB
public import DomainTheory.Neighborhood.Theorem111
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Exercise113.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise113

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB








/-- Two neighbourhoods present in a common element of `|B|` have comparable generating prefixes
(their cones cannot be disjoint, since the intersection is a nonempty cone). -/
theorem prefix_comparable_of_mem {σ τ : Str} (y : B.Element)
    (hσ : y.mem (cone σ)) (hτ : y.mem (cone τ)) : σ <+: τ ∨ τ <+: σ := by
  have hi : y.mem (cone σ ∩ cone τ) := y.inter_mem hσ hτ
  obtain ⟨ρ, hρ⟩ := y.sub hi
  rcases cone_trichotomy σ τ with h | h | h
  · exact Or.inr (cone_subset_cone.mp h)
  · exact Or.inl (cone_subset_cone.mp h)
  · exfalso
    have hmem : ρ ∈ cone ρ := mem_cone.mpr List.prefix_rfl
    rw [← hρ, h] at hmem
    simp at hmem

end DomainTheory.Neighborhood.Exercise113
