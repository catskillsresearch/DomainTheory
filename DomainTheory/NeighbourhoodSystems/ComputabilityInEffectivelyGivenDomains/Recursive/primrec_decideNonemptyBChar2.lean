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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_autStateCardFuelChar2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_matchesBChar2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_codeBound

@[expose] public section


namespace Domain.Recursive

















































































































































































































































open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

















































theorem primrec_decideNonemptyBChar2 :
    Nat.Primrec (fun s => decideNonemptyBChar s.unpair.1 s.unpair.2) := by
  have hg : Nat.Primrec (fun u => mulBit (allBinDigitsChar u.unpair.2.unpair.1)
      (matchesBChar u.unpair.1 u.unpair.2.unpair.2 u.unpair.2.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair
      (primrec_allBinDigitsChar.comp (Nat.Primrec.left.comp Nat.Primrec.right))
      (primrec_matchesBChar2.comp (Nat.Primrec.pair Nat.Primrec.left
        (Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
          (Nat.Primrec.left.comp Nat.Primrec.right)))))).of_eq fun u => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hbe := primrec_bExistsFn_param hg
  have hpack : Nat.Primrec (fun s => Nat.pair (Nat.pair s.unpair.1 s.unpair.2)
      (codeBound (autStateCardFuelChar s.unpair.1 s.unpair.2))) :=
    Nat.Primrec.pair (Nat.Primrec.pair Nat.Primrec.left Nat.Primrec.right)
      (primrec_codeBound.comp primrec_autStateCardFuelChar2)
  exact (hbe.comp hpack).of_eq fun s => by
    simp only [unpair_pair_fst, unpair_pair_snd, decideNonemptyBChar]

end Domain.Recursive
