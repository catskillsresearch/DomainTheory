/-ai
For a continuous lattice D, Scott's way-below neighbourhoods form a neighbourhood system on the token set D. Arbitrary filters need not be principal: the filter of neighbourhoods of elements below an element x has retraction equal to x but may properly contain the principal filter of x. The correct domain is the round filters, those for which membership of the neighbourhood of a yields a finer code b way-below which a lies and whose neighbourhood also belongs to the filter, and under continuity D is order-isomorphic to the round filters by the principal filter and its retraction. The abbreviation continuousLattice_to_neighborhoodSystem names this neighbourhood system.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toNeighborhoodSystem
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Round
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.domainOrderIso
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.domainEmbedding
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_bot
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_inter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_anti
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter_mono
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.mem_wayBelowUp_toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.bot_mem_codes
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes_nonempty
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes_directed
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.mem_wayBelowUp_ofFilter_of_round
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter_ofFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter_isRound
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter_toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.RoundFilter

@[expose] public section

/-!
# Continuous lattices → neighbourhood systems (1972 → 1980)

For a continuous lattice `D`, Scott’s way-below neighbourhoods
`↟a = { z | a ≪ z }` form a `NeighborhoodSystem` on token set `D`.

Arbitrary filters need not be principal (`{ ↟a | a ≤ x }` is a filter with
`ofFilter = x` but properly contains `toFilter x`). The correct domain is the
**round** filters: `↟a ∈ f` implies `∃ b, a ≪ b ∧ ↟b ∈ f`. Under
`IsContinuousLattice`, `D ≃o` round filters via `toFilter` / `ofFilter`.
-/

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice
open DomainTheory.NeighbourhoodSystems
open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]


section Continuous

variable (hD : IsContinuousLattice D)
include hD


end Continuous

end ContinuousLatticeToNeighborhood

/-- Blueprint name. -/
abbrev continuousLattice_to_neighborhoodSystem {D : Type*} [CompleteLattice D]
    (_hD : IsContinuousLattice D) : NeighborhoodSystem D :=
  ContinuousLatticeToNeighborhood.toNeighborhoodSystem
end DomainTheory.BridgeTheorems
