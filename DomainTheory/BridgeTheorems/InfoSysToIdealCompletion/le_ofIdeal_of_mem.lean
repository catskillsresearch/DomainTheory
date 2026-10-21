/-ai
A finite element of an ideal lies under the element determined by that ideal.

The element determined by the ideal is the directed supremum of the ideal's carrier, and the finite element is a member of that carrier.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.le_directedSup
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.ofIdeal

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem le_ofIdeal_of_mem {I : Ideal (FiniteElement A)} {y : FiniteElement A}
    (hy : y ∈ I) : (y : A.Element) ≤ ofIdeal A I :=
  A.le_directedSup _ _ _ ⟨y, hy, rfl⟩

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
