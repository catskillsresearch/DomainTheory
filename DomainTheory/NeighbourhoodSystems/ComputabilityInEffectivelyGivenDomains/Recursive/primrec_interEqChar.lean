module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_subsetBChar

@[expose] public section


namespace Domain.Recursive


open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722


theorem primrec_interEqChar :
    Nat.Primrec (fun s => interEqChar s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2) := by
  have hswap : Nat.Primrec (fun s : ℕ =>
      Nat.pair s.unpair.1 (Nat.pair s.unpair.2.unpair.2 s.unpair.2.unpair.1)) :=
    Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
        (Nat.Primrec.left.comp Nat.Primrec.right))
  have h1 := primrec_subsetBChar
  have h2 : Nat.Primrec (fun s => subsetBChar s.unpair.1 s.unpair.2.unpair.2 s.unpair.2.unpair.1) :=
    (primrec_subsetBChar.comp hswap).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_mulBit.comp (Nat.Primrec.pair h1 h2)).of_eq fun s => by
    simp only [unpair_pair_fst, unpair_pair_snd, interEqChar]

end Domain.Recursive
