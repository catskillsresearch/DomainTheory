/-ai
The relation beforeHalt is primitive recursive.

Inequality between the shifted halting enumerator on the first argument and the second argument is primitive recursive. Quantifying that inequality over the initial segment of length one more than the second argument, and rewriting by the definition of beforeHalt, gives the relation.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_haltEnum
public import DomainTheory.DataTypesAsLattices.Enumeration.beforeHalt
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem primrecPred_beforeHalt : PrimrecRel beforeHalt := by
  have hne : PrimrecRel fun (i m : ℕ) => haltEnum i ≠ m :=
    (Primrec.eq.comp (primrec_haltEnum.comp Primrec.fst) Primrec.snd).not
  exact (hne.forall_mem_list.comp (Primrec.list_range.comp
      (Primrec.succ.comp Primrec.snd)) Primrec.fst).of_eq fun _ => by
    simp [beforeHalt]

end DomainTheory.DataTypesAsLattices
