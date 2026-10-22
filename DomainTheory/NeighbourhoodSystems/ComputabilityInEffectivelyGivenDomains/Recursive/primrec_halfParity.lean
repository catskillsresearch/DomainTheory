/-ai
The function sending n to the pair of its quotient by 2 and its remainder modulo 2 is primitive recursive.

In the primitive-recursion state the previous value is the second component of the second component. The step that pairs the sum of the two components of that value with one minus its second component is primitive recursive. Primitive recursion from 0 with that step, composed with the pairing of the constant 0 and the identity, agrees with the function after simplifying the unpaired projections and the identity.
ai-/
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

@[expose] public section


namespace Domain.Recursive


theorem primrec_halfParity : Nat.Primrec halfParity := by
  have hIH : Nat.Primrec (fun w => w.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hstep : Nat.Primrec (fun w => Nat.pair (w.unpair.2.unpair.2.unpair.1 + w.unpair.2.unpair.2.unpair.2)
      (1 - w.unpair.2.unpair.2.unpair.2)) :=
    (primrec_add₂ (Nat.Primrec.left.comp hIH) (Nat.Primrec.right.comp hIH)).pair
      (primrec_sub₂ (Nat.Primrec.const 1) (Nat.Primrec.right.comp hIH))
  refine ((Nat.Primrec.prec (Nat.Primrec.const 0) hstep).comp
    ((Nat.Primrec.const 0).pair primrec_id)).of_eq (fun n => ?_)
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rfl

end Domain.Recursive
