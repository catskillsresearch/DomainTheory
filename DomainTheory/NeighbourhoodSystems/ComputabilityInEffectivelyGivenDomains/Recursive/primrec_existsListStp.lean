/-ai
If g is primitive recursive, then so is the disjunctive fold step of the bounded existential character.

The accumulator, the head, and the parameter are projections, and the equality-to-one test of g at the pair of the head and the parameter is primitive recursive. Selection of the constant 1 when the accumulator is set, and of that test otherwise, agrees with the step by definition.
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


theorem primrec_existsListStp {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (existsListStp g) := by
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hp : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcall : Nat.Primrec (fun w : ℕ => isOne (g (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) :=
    primrec_isOne.comp (hg.comp (hx.pair hp))
  exact (primrec_selectFn hacc (Nat.Primrec.const 1) hcall).of_eq fun _ => rfl

end Domain.Recursive
