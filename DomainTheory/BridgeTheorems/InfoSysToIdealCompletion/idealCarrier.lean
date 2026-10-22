/-ai
The carrier of an ideal of finite elements is the set of underlying elements of the members of the ideal.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Underlying set of elements of an ideal of finite elements. -/
def idealCarrier (I : Ideal (FiniteElement A)) : Set A.Element :=
  Subtype.val '' (I : Set (FiniteElement A))

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
