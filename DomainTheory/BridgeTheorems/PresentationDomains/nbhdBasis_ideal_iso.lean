module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open Order

open scoped DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

section InfoSysTriangle

variable {α : Type*} [DecidableEq α]

variable {ι β : Type*} [DecidableEq ι]

/-- Under a decidable neighbourhood basis, `|𝒟|` ↔ InfoSys domain ↔ ideal completion. -/
noncomputable def nbhdBasis_ideal_iso (B : NbhdBasis ι β) :
    B.system.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement B.toInfoSys) :=
  B.domainOrderIso.trans (InfoSysToIdealCompletion.domainOrderIso B.toInfoSys)

end InfoSysTriangle

end DomainTheory.BridgeTheorems
