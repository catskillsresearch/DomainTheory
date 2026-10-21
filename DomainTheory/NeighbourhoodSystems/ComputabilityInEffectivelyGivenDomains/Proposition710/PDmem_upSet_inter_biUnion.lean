/-ai
The intersection of the down-set of a neighbourhood with a finite union of down-sets is a power-domain neighbourhood.

Induction on the list, distributing the intersection over the union. The empty union gives the empty intersection, which is a power-domain neighbourhood. For a cons cell, the head term is a power-domain neighbourhood by the two-down-set lemma, and the tail is one by the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.upSetUnion_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.upSetUnion_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PDmem_upSet_inter

@[expose] public section

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
