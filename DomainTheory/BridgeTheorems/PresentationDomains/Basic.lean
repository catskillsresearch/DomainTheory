module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.BridgeTheorems.PresentationDomains.neighborhood_ideal_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.RoundInfoSysElement
public import DomainTheory.BridgeTheorems.PresentationDomains.presentation_domains_equiv

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.ContinuousLattice
open DomainTheory.NeighbourhoodSystems
open Order
open scoped DomainTheory.ContinuousLattice
open ContinuousLatticeToNeighborhood

section InfoSysTriangle
variable {α : Type*} [DecidableEq α]

variable {ι β : Type*} [DecidableEq ι]

noncomputable abbrev presentation_domains_equiv_infoSys (A : InfoSys α) :=
  neighborhood_ideal_iso A

end InfoSysTriangle

universe u
variable {D : Type u} [CompleteLattice D] [DecidableEq D]

section Continuous

variable (hD : ContinuousLattice D)
include hD

theorem exists_presentation_domains_equiv :
    Nonempty (D ≃o RoundInfoSysElement (D := D)) :=
  ⟨presentation_domains_equiv hD⟩

end Continuous
end DomainTheory.BridgeTheorems
