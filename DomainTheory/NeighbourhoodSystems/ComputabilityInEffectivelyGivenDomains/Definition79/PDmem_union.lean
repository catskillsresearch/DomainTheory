/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)



/-- **Definition 7.9 — closure under finite unions.** `ℙ𝒟` is closed under binary union
(concatenate the index lists); with `PDmem_empty` this gives closure under all finite unions,
which is exactly how Scott defines the family. -/
theorem PDmem_union {W₁ W₂ : Set (Set α)} (h₁ : V.PDmem W₁) (h₂ : V.PDmem W₂) :
    V.PDmem (W₁ ∪ W₂) := by
  obtain ⟨L₁, hL₁, rfl⟩ := h₁
  obtain ⟨L₂, hL₂, rfl⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro X hX
    rcases List.mem_append.mp hX with h | h
    · exact hL₁ X h
    · exact hL₂ X h
  · ext z
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop, List.mem_append]
    constructor
    · rintro (⟨X, hX, hz⟩ | ⟨X, hX, hz⟩)
      · exact ⟨X, Or.inl hX, hz⟩
      · exact ⟨X, Or.inr hX, hz⟩
    · rintro ⟨X, hX | hX, hz⟩
      · exact Or.inl ⟨X, hX, hz⟩
      · exact Or.inr ⟨X, hX, hz⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
