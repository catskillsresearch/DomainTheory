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
