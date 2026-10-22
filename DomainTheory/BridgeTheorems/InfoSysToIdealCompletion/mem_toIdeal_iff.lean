/-ai
A finite element belongs to the ideal associated with an element x if and only if it lies under x.

Membership in that ideal is membership among the finite approximants of x, which holds if and only if the finite element lies under x.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.Basic
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.mem_finiteApproximants_iff

@[expose] public section


namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)


theorem mem_toIdeal_iff {x : A.Element} {y : FiniteElement A} :
    y ∈ toIdeal A x ↔ (y : A.Element) ≤ x :=
  mem_finiteApproximants_iff A

end InfoSysToIdealCompletion
end DomainTheory.BridgeTheorems
