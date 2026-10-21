/-ai
The check relation holds of a domain set and a two-point set exactly when both are neighbourhoods and either the two-point set is the full set or the domain set differs from the master.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

@[simp] theorem check_rel {X : Set α} {Y : Set (Fin 2)} :
    (check : ApproximableMap D O).rel X Y ↔
      D.mem X ∧ O.mem Y ∧ (Y = ({0, 1} : Set (Fin 2)) ∨ X ≠ D.master) :=
  Iff.rfl

end DomainTheory.NeighbourhoodSystems
