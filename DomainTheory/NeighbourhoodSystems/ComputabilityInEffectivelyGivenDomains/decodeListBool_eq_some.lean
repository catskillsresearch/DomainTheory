/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
import all DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mapM_natBool_eq_some

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem decodeListBool_eq_some (n : ℕ) (σ : List Bool) (h : decodeListBool n = some σ) :
    n = encodeListBool σ := by
  have hl : decodeList n = σ.map boolNat := mapM_natBool_eq_some (decodeList n) σ h
  calc n = encodeList (decodeList n) := (encodeList_decodeList n).symm
    _ = encodeList (σ.map boolNat) := by rw [hl]
    _ = encodeListBool σ := rfl

end Exercise722

end DomainTheory.NeighbourhoodSystems
