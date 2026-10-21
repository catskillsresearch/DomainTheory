/-ai
If a fuel-bounded decode recovers an expression, then the depth of that expression is at most the fuel.

Induction on the fuel. Zero fuel never succeeds. At a successor, match the tag. Tag 0 yields sigma, of depth 1, when the payload is zero, and fails otherwise. Tag 1 yields a singleton, of depth 1, when the boolean list decodes. Tags 2 and 3 succeed only when both subcodes decode, and the inductive depth bounds together with one extra constructor stay within the successor fuel. A tag of the form t + 4 fails.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.sexprDepth
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_not_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_single
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_cap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_junk
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- **Fuel sufficiency:** the recovered expression never needs more depth than the fuel it was
decoded with. -/
theorem decodeFuel_depth_le {fuel c : ℕ} {e : SExpr} (h : decodeFuel fuel c = some e) :
    sexprDepth e ≤ fuel := by
  induction fuel generalizing c e with
  | zero => simp [decodeFuel] at h
  | succ fuel ih =>
    match tag : c.unpair.1 with
    | 0 =>
      by_cases hσ : c.unpair.2 = 0
      · rw [decodeFuel_succ_sigma fuel c tag hσ] at h
        simp only [Option.some.injEq] at h
        simp [← h, sexprDepth]
      · rw [decodeFuel_succ_not_sigma fuel c tag hσ] at h; simp at h
    | 1 =>
      rw [decodeFuel_succ_single fuel c tag] at h
      cases hb : decodeListBool c.unpair.2 with
      | none => simp [hb] at h
      | some σ =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        simp [← h, sexprDepth]
    | 2 =>
      rw [decodeFuel_succ_cat fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hda := ih ha
          have hdb := ih hb
          simp only [← h, sexprDepth]
          omega
    | 3 =>
      rw [decodeFuel_succ_cap fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hda := ih ha
          have hdb := ih hb
          simp only [← h, sexprDepth]
          omega
    | _ + 4 =>
      rw [decodeFuel_succ_junk fuel c (by omega)] at h; simp at h

end Exercise722

end DomainTheory.NeighbourhoodSystems
