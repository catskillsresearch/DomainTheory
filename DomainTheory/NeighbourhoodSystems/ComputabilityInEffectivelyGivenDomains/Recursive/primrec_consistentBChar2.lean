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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_decideNonemptyBChar2

@[expose] public section


namespace Domain.Recursive


open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722


/-- **`consistentBChar` is jointly primitive recursive in `(fuel, c1, c2)`.** -/
theorem primrec_consistentBChar2 :
    Nat.Primrec (fun s => consistentBChar s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2) := by
  have hpack : Nat.Primrec (fun s => Nat.pair s.unpair.1
      (Nat.pair 3 (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2))) :=
    Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.const 3)
        (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right)
          (Nat.Primrec.right.comp Nat.Primrec.right)))
  exact (primrec_decideNonemptyBChar2.comp hpack).of_eq fun s => by
    simp only [unpair_pair_fst, unpair_pair_snd, consistentBChar, capCode]

end Domain.Recursive
