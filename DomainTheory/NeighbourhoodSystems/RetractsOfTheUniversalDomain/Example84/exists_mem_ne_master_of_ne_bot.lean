/-ai
An element of a neighbourhood system that differs from bottom contains some neighbourhood other than the master.

Otherwise every neighbourhood of the element equals the master. Extensionality against bottom then identifies the element with bottom: a neighbourhood of the element is the master and so belongs to bottom, and a neighbourhood of bottom is the master and so belongs to the element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

/-- A non-bottom element of `D` always has *some* member neighbourhood other than the master.
(Classical: uses `by_contra`/`push_neg`, an allowed `Prop`-level use of `Classical.choice`.) -/
theorem exists_mem_ne_master_of_ne_bot {y : D.Element} (hy : y ≠ D.bot) :
    ∃ Z, y.mem Z ∧ Z ≠ D.master := by
  by_contra hcon
  push Not at hcon
  apply hy
  apply Element.ext
  intro Z
  rw [mem_bot]
  exact ⟨fun hZ => hcon Z hZ, fun hZ => hZ ▸ y.master_mem⟩

end DomainTheory.NeighbourhoodSystems
