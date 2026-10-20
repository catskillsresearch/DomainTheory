/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toNeighborhoodSystem
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.IsRound
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
