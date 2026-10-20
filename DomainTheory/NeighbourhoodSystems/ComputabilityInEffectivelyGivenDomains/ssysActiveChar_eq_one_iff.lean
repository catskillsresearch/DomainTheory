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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuelOkChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.c9b5_sexprDepth_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.c9b5_sexprGodelEncode_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_sound
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_depth_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem ssysActiveChar_eq_one_iff (n : ℕ) : ssysActiveChar n = 1 ↔ ssysActive n = true := by
  simp only [ssysActiveChar, ssysActive, SExpr.decode, mulBit_eq_one_iff,
    decodeFuelOkChar_eq_one_iff]
  cases hdec : decodeFuel (n.unpair.2 + 1) n.unpair.1 with
  | none => simp
  | some e =>
    have hc : n.unpair.1 = SExpr.encode e := decodeFuel_sound hdec
    have hdepth : Domain.Recursive.c9b5_sexprDepth e ≤ n.unpair.2 + 1 := by
      rw [c9b5_sexprDepth_eq]; exact decodeFuel_depth_le hdec
    simp only [Option.isSome_some, true_and]
    rw [hc, ← c9b5_sexprGodelEncode_eq, decideNonemptyBChar_eq_one_iff hdepth, decideNonemptyB_iff]

end Exercise722

end DomainTheory.NeighbourhoodSystems
