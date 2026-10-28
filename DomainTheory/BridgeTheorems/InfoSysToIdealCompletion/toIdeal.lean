module

public import Mathlib.Order.Ideal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.nonempty_finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.directed_finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.isLowerSet_finiteApproximants
public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def toIdeal (x : A.Element) : Ideal (FiniteElement A) where
  carrier := finiteApproximants A x
  lower' := isLowerSet_finiteApproximants A x
  nonempty' := nonempty_finiteApproximants A x
  directed' := directed_finiteApproximants A x

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
