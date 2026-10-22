/-ai
A filter f of the way-below neighbourhood system on a complete lattice D is round when membership of the way-below neighbourhood of an element a yields a code b with a way-below b whose way-below neighbourhood also belongs to f.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

/-- Roundness: `↟a ∈ f` is witnessed by a finer code `b` with `a ≪ b`. -/
def IsRound (f : Filter (D := D)) : Prop :=
  ∀ {a : D}, f.mem (wayBelowUp a) → ∃ b : D, a ≪ b ∧ f.mem (wayBelowUp b)

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
