module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.sexprDepth
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.c9b5_sexprDepth_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.c9b5_sexprGodelEncode_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_sound
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_depth_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar_le_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentBChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActive_exists_decode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem ssysConsistentBChar_eq_one_iff (n m : ℕ) :
    ssysConsistentBChar n m = 1 ↔ ssysConsistentB n m = true := by
  unfold ssysConsistentBChar ssysConsistentB
  by_cases hn : ssysActive n = true
  · by_cases hm : ssysActive m = true
    · have hnc : ssysActiveChar n = 1 := (ssysActiveChar_eq_one_iff n).mpr hn
      have hmc : ssysActiveChar m = 1 := (ssysActiveChar_eq_one_iff m).mpr hm
      obtain ⟨a, hdecn⟩ := ssysActive_exists_decode hn
      obtain ⟨b, hdecm⟩ := ssysActive_exists_decode hm
      have hac : n.unpair.1 = SExpr.encode a := decodeFuel_sound hdecn
      have hbc : m.unpair.1 = SExpr.encode b := decodeFuel_sound hdecm
      have hda : sexprDepth a ≤ n.unpair.2 + 1 := decodeFuel_depth_le hdecn
      have hdb : sexprDepth b ≤ m.unpair.2 + 1 := decodeFuel_depth_le hdecm
      have hfuel : Domain.Recursive.c9b5_sexprDepth (.cap a b) ≤ n.unpair.2 + m.unpair.2 + 2 := by
        rw [c9b5_sexprDepth_eq]
        simp only [sexprDepth]
        omega
      simp only [hnc, hmc, mulBit, mul_one, selectFn_one]
      rw [hac, hbc, ← c9b5_sexprGodelEncode_eq, ← c9b5_sexprGodelEncode_eq,
        consistentBChar_eq_one_iff hfuel]
      have hnotinactive : (!ssysActive n || !ssysActive m) = false := by simp [hn, hm]
      rw [hnotinactive, ite_eq_right (by decide)]
      simp only [hdecn, hdecm]
      exact (consistentB_iff a b).symm
    · have hm0 : ssysActiveChar m = 0 := by
        have hle := ssysActiveChar_le_one m
        have hne : ssysActiveChar m ≠ 1 := fun h => hm ((ssysActiveChar_eq_one_iff m).mp h)
        omega
      have hmf : ssysActive m = false := by
        cases hAm : ssysActive m with
        | false => rfl
        | true => exact absurd hAm hm
      simp only [hm0, mulBit, mul_zero, selectFn_zero, hmf, Bool.not_false, Bool.or_true, ite_true]
  · have hn0 : ssysActiveChar n = 0 := by
      have hle := ssysActiveChar_le_one n
      have hne : ssysActiveChar n ≠ 1 := fun h => hn ((ssysActiveChar_eq_one_iff n).mp h)
      omega
    have hnf : ssysActive n = false := by
      cases hAn : ssysActive n with
      | false => rfl
      | true => exact absurd hAn hn
    simp only [hn0, mulBit, zero_mul, selectFn_zero, hnf, Bool.not_false, Bool.true_or, ite_true]

end Exercise722

end DomainTheory.NeighbourhoodSystems
