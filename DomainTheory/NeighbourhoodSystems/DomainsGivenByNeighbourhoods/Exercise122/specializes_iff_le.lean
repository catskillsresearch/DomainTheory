/-ai
One element specializes to another if and only if the second approximates the first.

Specialization rewrites as the requirement that every open set containing the second element contains the first, and that requirement is the approximation of the first by the second.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Topology.Inseparable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.le_iff_isOpen_imp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- The approximation order `⊑` is the opposite of Mathlib's specialization preorder `⤳`:
`y ⤳ x ↔ x ⊑ y`. (Scott's (iii) says exactly that `⊑` is the specialization order of this
topology.) -/
theorem specializes_iff_le (x y : V.Element) : y ⤳ x ↔ x ≤ y := by
  rw [specializes_iff_forall_open]
  exact (V.le_iff_isOpen_imp x y).symm

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
