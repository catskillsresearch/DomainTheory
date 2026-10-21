/-ai
A finite element is a finite approximant of an element x if and only if it lies under x.

One direction is that every finite approximant lies under x, and the other is that every finite element below x is a finite approximant.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.Basic

@[expose] public section


namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)


theorem mem_finiteApproximants_iff {x : A.Element} {y : FiniteElement A} :
    y ∈ finiteApproximants A x ↔ (y : A.Element) ≤ x :=
  ⟨le_of_mem_finiteApproximants A, mem_finiteApproximants_of_le A⟩

end InfoSysToIdealCompletion
end DomainTheory.BridgeTheorems
