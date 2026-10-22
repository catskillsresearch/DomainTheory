module

public import DomainTheory.BridgeTheorems.PresentationDomains.continuousLattice_roundInfoSys_iso
public import Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice
public import DomainTheory.BridgeTheorems.PresentationDomains.RoundInfoSysElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open Order

open scoped DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

universe u

variable {D : Type u} [CompleteLattice D] [DecidableEq D]

section Continuous

variable (hD : ContinuousLattice D)

include hD

/-- **Blueprint:** three-presentation equivalence for continuous lattices.

`D ≃o RoundFilter ≃o RoundInfoSysElement`, with the `↟`-system’s `NbhdBasis`
supplying the 1980↔1982 coding. (Raw `|𝒟|` / full `|A|` remain larger.) -/
noncomputable def presentation_domains_equiv :
    D ≃o RoundInfoSysElement (D := D) :=
  continuousLattice_roundInfoSys_iso hD

end Continuous

end DomainTheory.BridgeTheorems
