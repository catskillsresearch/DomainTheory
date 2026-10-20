module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.ApproximableMap₂

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem

/-- **Exercise 2.11 — directed union (indexed form).** For a directed family `a : I → |𝒟|` (any two
`a i, a j` have a common upper bound `a k`), the union `⋃ᵢ a i` is again an element of `|𝒟|`. Built
on `sSupDirected` over the range. -/
def iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) : V.Element :=
  V.sSupDirected (Set.range a) (Set.range_nonempty a) (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨a k, ⟨k, rfl⟩, hik, hjk⟩)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
