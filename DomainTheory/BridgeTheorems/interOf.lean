/-ai
The intersection coded by a finite set of neighbourhood indices is the fold of binary intersection over the indexed neighbourhoods, starting from the master set, so that the empty intersection is the master set.
ai-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

/-- Finite intersection of coded neighbourhoods, with Scott’s convention `⋂∅ = Δ`. -/
def interOf (u : Finset ι) : Set α :=
  u.fold (· ∩ ·) B.system.master B.nbhd

end NbhdBasis

end DomainTheory.BridgeTheorems
