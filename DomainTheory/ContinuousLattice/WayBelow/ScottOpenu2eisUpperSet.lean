/-ai
A Scott-open set is an upper set.

The upper-set property is the first component of Scott-openness.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


theorem ScottOpen.isUpperSet {U : Set D} (h : ScottOpen U) : IsUpperSet U := h.1

end DomainTheory.ContinuousLattice
