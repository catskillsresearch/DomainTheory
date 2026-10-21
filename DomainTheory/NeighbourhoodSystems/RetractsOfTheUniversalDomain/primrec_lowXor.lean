/-ai
The function sending a paired natural number to the low-bit exclusive disjunction of its two components is primitive recursive.

Reduce each component modulo 2, add the results, and reduce modulo 2. The composite agrees with the definition by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.lowXor

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_lowXor : Nat.Primrec (fun t => lowXor t.unpair.1 t.unpair.2) :=
  (primrec_mod2.comp
    (primrec_add₂ (primrec_mod2.comp Nat.Primrec.left) (primrec_mod2.comp Nat.Primrec.right))).of_eq
    fun _ => rfl

end DomainTheory.NeighbourhoodSystems
