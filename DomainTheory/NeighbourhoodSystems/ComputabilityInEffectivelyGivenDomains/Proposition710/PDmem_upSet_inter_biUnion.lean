module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.upSetUnion_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.upSetUnion_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PDmem_upSet_inter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `↓X ∩ (⋃_{Y ∈ L} ↓Y) ∈ ℙ𝒟`: distribute `∩` over the finite union and use `PDmem_upSet_inter`
term by term. -/
theorem PDmem_upSet_inter_biUnion {X : Set α} (hX : V.mem X) :
    ∀ (L : List (Set α)), (∀ Y ∈ L, V.mem Y) → V.PDmem (V.upSet X ∩ ⋃ Y ∈ L, V.upSet Y) := by
  intro L
  induction L with
  | nil =>
    intro _
    rw [V.upSetUnion_nil, Set.inter_empty]
    exact V.PDmem_empty
  | cons Y L ih =>
    intro hL
    rw [V.upSetUnion_cons, Set.inter_union_distrib_left]
    exact V.PDmem_union (V.PDmem_upSet_inter hX (hL Y (List.mem_cons.mpr (Or.inl rfl))))
      (ih (fun Z hZ => hL Z (List.mem_cons.mpr (Or.inr hZ))))

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
