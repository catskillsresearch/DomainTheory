module

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

/-- Finite (compact) elements: closures of consistent finite token sets. -/
abbrev FiniteElement : Type _ :=
  { x : A.Element // ∃ (u : Finset α) (hu : u ∈ A.Con), x = A.closure u hu }

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
