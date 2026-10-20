module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

variable (u : D.Element) (hu : u ≠ D.bot)

@[simp] theorem mem_fixOfO {t : O.Element} {Z : Set α} :
    (fixOfO u t).mem Z ↔ D.mem Z ∧ (Z = D.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ u.mem Z)) :=
  Iff.rfl

end DomainTheory.NeighbourhoodSystems
