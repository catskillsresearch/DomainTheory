module

public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


theorem scottOpen_inter {U V : Set D} (hU : ScottOpen U) (hV : ScottOpen V) :
    ScottOpen (U ∩ V) := by
  refine ⟨hU.1.inter hV.1, fun S hS hSdir hmem => ?_⟩
  obtain ⟨s₁, hs₁S, hs₁U⟩ := hU.2 hS hSdir hmem.1
  obtain ⟨s₂, hs₂S, hs₂V⟩ := hV.2 hS hSdir hmem.2
  obtain ⟨s₃, hs₃S, h₁, h₂⟩ := hSdir s₁ hs₁S s₂ hs₂S
  exact ⟨s₃, hs₃S, hU.1 h₁ hs₁U, hV.1 h₂ hs₂V⟩

end DomainTheory.ContinuousLattice
