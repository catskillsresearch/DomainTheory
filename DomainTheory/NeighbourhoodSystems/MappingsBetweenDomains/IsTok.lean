/-ai
A set is a token for a family C of sets when it is finite and contained in some member of C.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-- A token: a finite set included in some member of `C`. -/
class IsTok (F : Set τ) : Prop where
  out : F.Finite ∧ ∃ X ∈ C, F ⊆ X

end DomainTheory.NeighbourhoodSystems.Exercise222
