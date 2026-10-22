module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.finalSegmentSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.mem_def
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.master_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

/-- Each `Set.Ici a` is a (non-empty, upper) neighbourhood. -/
theorem Ici_mem (a : Δ) : (finalSegmentSystem Δ).mem (Set.Ici a) :=
  ⟨⟨a, le_refl a⟩, isUpperSet_Ici a⟩

end FinalSegment

end DomainTheory.NeighbourhoodSystems
