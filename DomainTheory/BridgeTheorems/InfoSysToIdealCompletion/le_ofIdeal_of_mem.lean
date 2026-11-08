module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.ofIdeal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.directedSup
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.factoid_45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem le_ofIdeal_of_mem {I : Ideal (FiniteElement A)} {y : FiniteElement A}
    (hy : y ∈ I) : (y : A.Element) ≤ ofIdeal A I :=
  InfoSys.directedSup.le_of_mem A _ _ _ ⟨y, hy, rfl⟩

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
