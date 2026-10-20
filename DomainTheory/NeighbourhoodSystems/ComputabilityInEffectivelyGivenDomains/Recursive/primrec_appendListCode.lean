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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_appendListTabFn

@[expose] public section


namespace Domain.Recursive











































































































































































































































theorem primrec_appendListCode : Nat.Primrec (fun t => appendListCode t.unpair.1 t.unpair.2) := by
  have hc1 := Nat.Primrec.left
  have hc2 := Nat.Primrec.right
  have hlen1 := primrec_listLenChar.comp hc1
  have hlen2 := primrec_listLenChar.comp hc2
  have hsum := primrec_add₂ hlen1 hlen2
  have hp := hc1.pair (hc2.pair hlen1)
  have hr := (hsum.pair hp).pair hsum
  refine ((primrec_tabCode primrec_appendListTabFn).comp hr).of_eq fun t => by
    unfold appendListCode
    simp only [unpair_pair_fst, unpair_pair_snd]

end Domain.Recursive
