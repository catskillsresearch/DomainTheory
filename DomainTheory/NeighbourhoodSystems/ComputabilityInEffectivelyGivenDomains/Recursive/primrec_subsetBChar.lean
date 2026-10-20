module

public import Mathlib.Data.Nat.Sqrt
import all Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
import all Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
import all Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_pow
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_powu2082
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_bForallFn_param
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_autStateCardFuelChar2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_matchesBChar2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_codeBound

@[expose] public section


namespace Domain.Recursive

















































































































































































































































open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722























































theorem primrec_subsetBChar :
    Nat.Primrec (fun s => subsetBChar s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2) := by
  have hg : Nat.Primrec (fun u => selectFn
      (subsetGuardChar u.unpair.1 u.unpair.2.unpair.2.unpair.1 u.unpair.2.unpair.2.unpair.2
        u.unpair.2.unpair.1)
      (selectFn (matchesBChar u.unpair.1 u.unpair.2.unpair.2.unpair.1 u.unpair.2.unpair.1)
        (matchesBChar u.unpair.1 u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1) 1) 1) := by
    have hfuel : Nat.Primrec (fun u : ℕ => u.unpair.1) := Nat.Primrec.left
    have hi : Nat.Primrec (fun u : ℕ => u.unpair.2.unpair.1) :=
      Nat.Primrec.left.comp Nat.Primrec.right
    have hc1 : Nat.Primrec (fun u : ℕ => u.unpair.2.unpair.2.unpair.1) :=
      Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
    have hc2 : Nat.Primrec (fun u : ℕ => u.unpair.2.unpair.2.unpair.2) :=
      Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
    have hguard : Nat.Primrec (fun u => subsetGuardChar u.unpair.1 u.unpair.2.unpair.2.unpair.1
        u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1) := by
      have hbound : Nat.Primrec (fun u => subsetBoundChar u.unpair.1
          u.unpair.2.unpair.2.unpair.1 u.unpair.2.unpair.2.unpair.2) := by
        have h1 : Nat.Primrec (fun u => autStateCardFuelChar u.unpair.1
            u.unpair.2.unpair.2.unpair.1) := by
          have := primrec_autStateCardFuelChar2
          exact (this.comp (Nat.Primrec.pair hfuel hc1)).of_eq fun u => by
            simp only [unpair_pair_fst, unpair_pair_snd]
        have h2 : Nat.Primrec (fun u => autStateCardFuelChar u.unpair.1
            u.unpair.2.unpair.2.unpair.2) := by
          have := primrec_autStateCardFuelChar2
          exact (this.comp (Nat.Primrec.pair hfuel hc2)).of_eq fun u => by
            simp only [unpair_pair_fst, unpair_pair_snd]
        exact (primrec_mul₂ (primrec_pow₂ (Nat.Primrec.const 2) h1)
          (primrec_pow₂ (Nat.Primrec.const 2) h2))
      exact (primrec_mulBit.comp (Nat.Primrec.pair
        (primrec_allBinDigitsChar.comp hi)
        (primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1)
          (primrec_sub₂ (primrec_listLenChar.comp hi) hbound))))).of_eq fun u => by
        simp only [unpair_pair_fst, unpair_pair_snd, subsetGuardChar, mulBit]
    have hm1 : Nat.Primrec (fun u => matchesBChar u.unpair.1 u.unpair.2.unpair.2.unpair.1
        u.unpair.2.unpair.1) := by
      have := primrec_matchesBChar2
      exact (this.comp (Nat.Primrec.pair hfuel (Nat.Primrec.pair hc1 hi))).of_eq fun u => by
        simp only [unpair_pair_fst, unpair_pair_snd]
    have hm2 : Nat.Primrec (fun u => matchesBChar u.unpair.1 u.unpair.2.unpair.2.unpair.2
        u.unpair.2.unpair.1) := by
      have := primrec_matchesBChar2
      exact (this.comp (Nat.Primrec.pair hfuel (Nat.Primrec.pair hc2 hi))).of_eq fun u => by
        simp only [unpair_pair_fst, unpair_pair_snd]
    exact primrec_selectFn hguard (primrec_selectFn hm1 hm2 (Nat.Primrec.const 1))
      (Nat.Primrec.const 1)
  have hb := primrec_bForallFn_param hg
  have hpack : Nat.Primrec (fun s => Nat.pair
      (Nat.pair s.unpair.1 (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2))
      (codeBound (subsetBoundChar s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2))) := by
    have hfuel : Nat.Primrec (fun s : ℕ => s.unpair.1) := Nat.Primrec.left
    have hc1 : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) :=
      Nat.Primrec.left.comp Nat.Primrec.right
    have hc2 : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) :=
      Nat.Primrec.right.comp Nat.Primrec.right
    have h1 : Nat.Primrec (fun s => autStateCardFuelChar s.unpair.1 s.unpair.2.unpair.1) := by
      have := primrec_autStateCardFuelChar2
      exact (this.comp (Nat.Primrec.pair hfuel hc1)).of_eq fun s => by
        simp only [unpair_pair_fst, unpair_pair_snd]
    have h2 : Nat.Primrec (fun s => autStateCardFuelChar s.unpair.1 s.unpair.2.unpair.2) := by
      have := primrec_autStateCardFuelChar2
      exact (this.comp (Nat.Primrec.pair hfuel hc2)).of_eq fun s => by
        simp only [unpair_pair_fst, unpair_pair_snd]
    have hbnd : Nat.Primrec (fun s => subsetBoundChar s.unpair.1 s.unpair.2.unpair.1
        s.unpair.2.unpair.2) :=
      primrec_mul₂ (primrec_pow₂ (Nat.Primrec.const 2) h1) (primrec_pow₂ (Nat.Primrec.const 2) h2)
    exact Nat.Primrec.pair (Nat.Primrec.pair hfuel (Nat.Primrec.pair hc1 hc2))
      (primrec_codeBound.comp hbnd)
  exact (hb.comp hpack).of_eq fun s => by
    simp only [unpair_pair_fst, unpair_pair_snd, subsetBChar]

end Domain.Recursive
