/-ai
If an index belongs to a finite set of indices, the folded intersection of the corresponding basis neighbourhoods is contained in the neighbourhood of that index.

A point of the folded intersection lies in every neighbourhood indexed by the set, by the membership rule for the folded intersection, and therefore lies in the neighbourhood of the given index.
ai-/
module

public import Mathlib.Data.Finset.Fold
import all Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.mem_interOf

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem interOf_subset_nbhd {u : Finset ι} {i : ι} (hi : i ∈ u) :
    B.interOf u ⊆ B.nbhd i := fun _ hx => (B.mem_interOf.mp hx).2 i hi

end NbhdBasis

end DomainTheory.BridgeTheorems
