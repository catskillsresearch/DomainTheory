/-ai
The code-level minimum of first components is primitive recursive.

The step applying the rational minimum to the pair of the inner first unpairing and the first unpairing of the outer first unpairing is primitive recursive by composition, identified by reflexivity. Primitive recursion of code folding with constant parameter zero, constant seed the one code, and the identity, identified by reflexivity, is the minimum code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFstCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_listMinFstCode : Nat.Primrec listMinFstCode := by
  have hstp : Nat.Primrec
      (fun t : ℕ => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1)) :=
    (primrec_ratMinCode.comp ((Nat.Primrec.left.comp Nat.Primrec.right).pair
      (Nat.Primrec.left.comp Nat.Primrec.left))).of_eq fun _ => rfl
  exact (primrec_foldCode hstp (Nat.Primrec.const 0) (Nat.Primrec.const oneCode) primrec_id).of_eq
    fun _ => rfl

end DomainTheory.NeighbourhoodSystems
