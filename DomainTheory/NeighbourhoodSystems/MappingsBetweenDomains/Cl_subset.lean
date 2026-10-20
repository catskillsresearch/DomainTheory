module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-- `F̄ ⊆ X` whenever `X ∈ C` contains `F`: the closure is the *smallest* member of `C` over `F`. -/
theorem Cl_subset {F X : Set τ} (hX : X ∈ C) (hFX : F ⊆ X) : Cl C F ⊆ X := by
  intro t ht
  exact (Set.mem_sInter.mp ht) X ⟨hX, hFX⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
