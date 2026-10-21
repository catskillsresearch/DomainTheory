/-ai
The code-level maximum of second components is primitive recursive.

The step applying the rational maximum to the pair of the inner first unpairing and the second unpairing of the outer first unpairing is primitive recursive by composition, identified by reflexivity. Primitive recursion of code folding with constant parameter zero, constant seed the zero code, and the identity, identified by reflexivity, is the maximum code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSndCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_listMaxSndCode : Nat.Primrec listMaxSndCode := by
  have hstp : Nat.Primrec
      (fun t : ℕ => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) :=
    (primrec_ratMaxCode.comp ((Nat.Primrec.left.comp Nat.Primrec.right).pair
      (Nat.Primrec.right.comp Nat.Primrec.left))).of_eq fun _ => rfl
  exact (primrec_foldCode hstp (Nat.Primrec.const 0) (Nat.Primrec.const zeroCode) primrec_id).of_eq
    fun _ => rfl

end DomainTheory.NeighbourhoodSystems
