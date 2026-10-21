/-ai
The order isomorphism from the basic-open neighbourhood filters of an information system to the ideal completion of its finite elements is the composite of the inverse domain isomorphism, from filters back to elements, and the ideal-completion isomorphism.
ai-/
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

/-- Neighbourhood filters of `|A|` ↔ ideals of finite elements (via `|A|`). -/
noncomputable def neighborhood_ideal_iso (A : InfoSys α) :
    (InfoSysToNeighborhood.toNeighborhoodSystem A).Element ≃o
      Ideal (InfoSysToIdealCompletion.FiniteElement A) :=
  (InfoSysToNeighborhood.domainOrderIso A).symm.trans
    (InfoSysToIdealCompletion.domainOrderIso A)

end InfoSysTriangle

end DomainTheory.BridgeTheorems
