module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Basic

@[expose] public section


namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice
open DomainTheory.NeighbourhoodSystems
open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]












theorem mem_codes_iff {f : Filter (D := D)} {a : D} :
    a ∈ codes f ↔ f.mem (wayBelowUp a) :=
  Iff.rfl

end ContinuousLatticeToNeighborhood
end DomainTheory.BridgeTheorems
