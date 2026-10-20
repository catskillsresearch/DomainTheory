module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fin2_zero_ne_zero_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap_check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_fixOfO

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

variable (u : D.Element) (hu : u ≠ D.bot)

/-- `fixOfO` and `check.toElementMap` intertwine `a` and the identity on `D`: applying `fixOfO`
after `check.toElementMap` recovers `a` itself. -/
theorem fixOfO_check_toElementMap (x : D.Element) :
    fixOfO u (check.toElementMap x) = (a u).toElementMap x := by
  apply Element.ext
  intro Z
  rw [mem_fixOfO, mem_toElementMap_a]
  have hcheck : (check.toElementMap x).mem ({0} : Set (Fin 2)) ↔ x ≠ D.bot := by
    rw [mem_toElementMap_check]
    constructor
    · rintro ⟨-, h | h⟩
      · exact absurd h fin2_zero_ne_zero_one
      · exact h
    · intro h; exact ⟨O_mem_zero, Or.inr h⟩
  rw [hcheck]

end DomainTheory.NeighbourhoodSystems
