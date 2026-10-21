/-ai
The folded intersection of a singleton index is the basis neighbourhood of that index.

Folding a singleton cuts the neighbourhood with the master set, and the neighbourhood is contained in the master set, so the cut is the neighbourhood itself.
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
public import DomainTheory.BridgeTheorems.nbhd_subset_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem interOf_singleton (a : ι) : B.interOf ({a} : Finset ι) = B.nbhd a := by
  simp [interOf, Finset.fold_singleton, Set.inter_eq_left.mpr (B.nbhd_subset_master a)]

end NbhdBasis

end DomainTheory.BridgeTheorems
