/-ai
If a fuel-bounded decode of a code recovers an expression, then the code is the Gödel code of that expression.

Induction on the fuel. Zero fuel never succeeds. At a successor, match the tag. Tag 0 with payload zero forces the code to be the pairing of zero with zero, the code of sigma, by inverting pairing; any other payload fails. Tag 1 recovers a boolean list, and the payload equals the boolean-list code of that list. Tags 2 and 3 recover both subexpressions by the inductive hypothesis and reassemble the nested pairing, again by inverting pairing. A tag of the form t + 4 fails.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_not_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_single
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_cap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_junk
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool_eq_some

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- **Soundness:** any code `c` that `decodeFuel` accepts is the canonical `SExpr.encode` of the
recovered expression (`decodeList`/`decodeListBool`/`Nat.pair` are all injective in the relevant
direction, so nothing "junk" can decode). -/
theorem decodeFuel_sound {fuel c : ℕ} {e : SExpr} (h : decodeFuel fuel c = some e) :
    c = SExpr.encode e := by
  induction fuel generalizing c e with
  | zero => simp [decodeFuel] at h
  | succ fuel ih =>
    match tag : c.unpair.1 with
    | 0 =>
      by_cases hσ : c.unpair.2 = 0
      · have hc : c = Nat.pair 0 0 := by
          have hpu := Nat.pair_unpair c; rw [tag, hσ] at hpu; exact hpu.symm
        rw [decodeFuel_succ_sigma fuel c tag hσ] at h
        simp only [Option.some.injEq] at h
        simp [SExpr.encode, ← h, hc]
      · rw [decodeFuel_succ_not_sigma fuel c tag hσ] at h; simp at h
    | 1 =>
      have hc1 : c = Nat.pair 1 c.unpair.2 := by
        have hpu := Nat.pair_unpair c; rw [tag] at hpu; exact hpu.symm
      rw [decodeFuel_succ_single fuel c tag] at h
      cases hb : decodeListBool c.unpair.2 with
      | none => simp [hb] at h
      | some σ =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have hσc : c.unpair.2 = encodeListBool σ := decodeListBool_eq_some c.unpair.2 σ hb
        rw [← h, SExpr.encode, hc1, hσc]
    | 2 =>
      have hc2 : c = Nat.pair 2 c.unpair.2 := by
        have hpu := Nat.pair_unpair c; rw [tag] at hpu; exact hpu.symm
      rw [decodeFuel_succ_cat fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hac : c.unpair.2.unpair.1 = SExpr.encode a := ih ha
          have hbc : c.unpair.2.unpair.2 = SExpr.encode b := ih hb
          have hpc : c.unpair.2 = Nat.pair (SExpr.encode a) (SExpr.encode b) := by
            have hpu := Nat.pair_unpair c.unpair.2; rw [hac, hbc] at hpu; exact hpu.symm
          rw [← h, SExpr.encode, hc2, hpc]
    | 3 =>
      have hc3 : c = Nat.pair 3 c.unpair.2 := by
        have hpu := Nat.pair_unpair c; rw [tag] at hpu; exact hpu.symm
      rw [decodeFuel_succ_cap fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hac : c.unpair.2.unpair.1 = SExpr.encode a := ih ha
          have hbc : c.unpair.2.unpair.2 = SExpr.encode b := ih hb
          have hpc : c.unpair.2 = Nat.pair (SExpr.encode a) (SExpr.encode b) := by
            have hpu := Nat.pair_unpair c.unpair.2; rw [hac, hbc] at hpu; exact hpu.symm
          rw [← h, SExpr.encode, hc3, hpc]
    | _ + 4 =>
      rw [decodeFuel_succ_junk fuel c (by omega)] at h; simp at h

end Exercise722

end DomainTheory.NeighbourhoodSystems
