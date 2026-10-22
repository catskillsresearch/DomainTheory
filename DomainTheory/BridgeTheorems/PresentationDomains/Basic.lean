/-ai
For an information system, the domain, the filters of its basic-open neighbourhood system, and the ideal completion of its finite elements determine the same ordered set. The abbreviation presentation_domains_equiv_infoSys names the order isomorphism from those neighbourhood filters to the ideal completion. The same triangle, starting from the filter domain, is available for a neighbourhood system with a decidable basis. The points of a continuous lattice correspond to its round way-below filters. When equality on the lattice is decidable, the way-below neighbourhood system has a basis indexed by the carrier, and the round filters correspond to the round elements of the induced information system, which then enter the ideal-completion triangle. The full filter domain and the full information-system domain properly contain these round parts.

A continuous lattice is order-isomorphic to the round elements of the information system induced by its way-below neighbourhood basis.

The presentation-domains equivalence is a witness.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice
public import DomainTheory.BridgeTheorems.PresentationDomains.neighborhood_ideal_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.nbhdBasis_ideal_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.wayBelowNbhdBasis
public import DomainTheory.BridgeTheorems.PresentationDomains.IsRoundInfoSysElement
public import DomainTheory.BridgeTheorems.PresentationDomains.roundFilter_infoSys_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.continuousLattice_roundFilter_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.continuousLattice_roundInfoSys_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.roundInfoSys_ideal_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.presentation_domains_equiv
public import DomainTheory.BridgeTheorems.PresentationDomains.presentation_domains_equiv_ideal
public import DomainTheory.BridgeTheorems.PresentationDomains.RoundInfoSysElement

@[expose] public section

/-!
# Presentation domain equivalences

## InfoSys / neighbourhood / ideal (constructive)

For any information system `A`:
`|A| ≃o` basic-open neighbourhood filters ≃o `Ideal (FiniteElement A)`.

Under a decidable `NbhdBasis`, the same triangle starts from `|𝒟|`.

## Continuous lattices (1972 corner)

Points of a continuous lattice `D` are **round** `↟`-filters, not arbitrary filters:
`D ≃o RoundFilter`. With `DecidableEq D`, the `↟`-system admits an `NbhdBasis`,
so round filters transport to a subtype of the induced InfoSys domain (and thence
into the ideal-completion triangle). The full (non-round) `|𝒟|` / `|A|` is properly
larger.
-/

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


/-- Constructive 1980↔1982↔ideal triangle for InfoSys domains. -/
noncomputable abbrev presentation_domains_equiv_infoSys (A : InfoSys α) :=
  neighborhood_ideal_iso A

end InfoSysTriangle

/-! ## Continuous lattice presentations via round `↟`-filters -/

universe u
variable {D : Type u} [CompleteLattice D] [DecidableEq D]


section Continuous

variable (hD : IsContinuousLattice D)
include hD


/-- The three presentations determine the same domain (round corner). -/
theorem exists_presentation_domains_equiv :
    Nonempty (D ≃o RoundInfoSysElement (D := D)) :=
  ⟨presentation_domains_equiv hD⟩

end Continuous
end DomainTheory.BridgeTheorems
