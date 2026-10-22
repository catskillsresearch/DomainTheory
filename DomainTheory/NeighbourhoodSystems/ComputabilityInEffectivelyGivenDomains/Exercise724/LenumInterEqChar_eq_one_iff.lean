
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_consSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.consSet_empty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.isPrefixChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.isPrefixChar_le_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Lenum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LenumInterEqChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mulBit_eq_zero_or_one

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

theorem LenumInterEqChar_eq_one_iff (n m k : ℕ) :
    LenumInterEqChar n m k = 1 ↔
      (isPrefixChar m n = 1 ∧ decodeList k = decodeList n) ∨
      (isPrefixChar n m = 1 ∧ decodeList k = decodeList m) := by
  have hstep : LenumInterEqChar n m k = 1 ↔
      mulBit (isPrefixChar m n) (listEqChar k n) = 1 ∨
      mulBit (isPrefixChar n m) (listEqChar k m) = 1 := by
    unfold LenumInterEqChar
    rcases mulBit_eq_zero_or_one (isPrefixChar_le_one m n) (listEqChar_le_one k n) with ha | ha <;>
      rcases mulBit_eq_zero_or_one (isPrefixChar_le_one n m) (listEqChar_le_one k m) with hb | hb <;>
        simp [ha, hb]
  rw [hstep, mulBit_eq_one_iff, mulBit_eq_one_iff, listEqChar_eq_one_iff, listEqChar_eq_one_iff]

end DomainTheory.NeighbourhoodSystems.Exercise724
