/-ai
One element of the two-point system lies under another if and only if membership of the singleton of zero passes from the first element to the second.

In one direction the order preserves that membership. In the other, a neighbourhood of the first element is a neighbourhood of the system, hence the singleton, which the hypothesis places in the second element, or the master, which belongs to the second element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_fixOfO

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

variable (u : D.Element) (hu : u ≠ D.bot)

theorem O_le_iff {t t' : O.Element} :
    t ≤ t' ↔ (t.mem ({0} : Set (Fin 2)) → t'.mem ({0} : Set (Fin 2))) := by
  constructor
  · intro h; exact h _
  · intro h Y hY
    rcases O_mem_iff.mp (t.sub hY) with rfl | rfl
    · exact h hY
    · exact t'.master_mem

end DomainTheory.NeighbourhoodSystems
