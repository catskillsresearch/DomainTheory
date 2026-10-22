/-ai
If a set is recursively enumerable, then the predicate that some positive number lies in it is recursively enumerable.

That predicate is the existential quantification of membership of a successor, and membership of a successor is the recursively enumerable membership predicate composed with the successor on the second component. The resulting predicate is exactly the stated one.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.hasPos {z : Pomega} (hz : IsRE z) : REPred fun _ : ℕ => ∃ k, k + 1 ∈ z :=
  _root_.REPred.of_eq
    (REPred.exists (p := fun _ k => k + 1 ∈ z)
      (hz.out.comp (Primrec.succ.to_comp.comp Computable.snd)))
    fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices
