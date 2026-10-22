module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.finiteApproximants
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Finite approximants of `x`, as `FiniteElement`s. -/
def finiteApproximants (x : A.Element) : Set (FiniteElement A) :=
  { y | (y : A.Element) ∈ A.finiteApproximants x }

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
