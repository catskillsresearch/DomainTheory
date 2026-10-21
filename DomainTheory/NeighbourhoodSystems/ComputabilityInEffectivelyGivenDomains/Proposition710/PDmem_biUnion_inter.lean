/-ai
The intersection of a finite union of down-sets with a power-domain neighbourhood is again a power-domain neighbourhood.

Induction on the list. The empty union meets the neighbourhood in the empty set, which is a power-domain neighbourhood. For a cons cell, the union distributes over the intersection on the right. The head down-set meets the second neighbourhood, presented as a finite union of down-sets, in a power-domain neighbourhood, and the tail does so by the inductive hypothesis, so their union is a power-domain neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.upSetUnion_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.upSetUnion_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PDmem_upSet_inter_biUnion

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `(⋃_{X ∈ L₁} ↓X) ∩ W₂ ∈ ℙ𝒟` for any `ℙ𝒟`-neighbourhood `W₂` (induction on `L₁`). -/
theorem PDmem_biUnion_inter :
    ∀ (L₁ : List (Set α)), (∀ X ∈ L₁, V.mem X) → ∀ {W₂ : Set (Set α)}, V.PDmem W₂ →
      V.PDmem ((⋃ X ∈ L₁, V.upSet X) ∩ W₂) := by
  intro L₁
  induction L₁ with
  | nil =>
    intro _ W₂ _
    rw [V.upSetUnion_nil, Set.empty_inter]
    exact V.PDmem_empty
  | cons X L ih =>
    intro hL W₂ hW₂
    rw [V.upSetUnion_cons, Set.union_inter_distrib_right]
    refine V.PDmem_union ?_ (ih (fun Z hZ => hL Z (List.mem_cons.mpr (Or.inr hZ))) hW₂)
    obtain ⟨L₂, hL₂, rfl⟩ := hW₂
    exact V.PDmem_upSet_inter_biUnion (hL X (List.mem_cons.mpr (Or.inl rfl))) L₂ hL₂

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
