module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.idealCarrier

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem nonempty_idealCarrier (I : Ideal (FiniteElement A)) :
    (idealCarrier A I).Nonempty := by
  obtain ⟨y, hy⟩ := I.nonempty
  exact ⟨y, y, hy, rfl⟩

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
