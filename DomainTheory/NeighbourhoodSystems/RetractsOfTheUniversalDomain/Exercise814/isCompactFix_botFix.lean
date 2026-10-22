/-ai
The bottom fixed point of a closure operator is compact among fixed points.

A nonempty directed family of fixed points has some index, and the bottom fixed point lies below the value of the family at that index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.botFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.botFix_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsCompactFix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section ClosureOperator

variable {a : ApproximableMap E E}

/-- `botFix` is compact: it is below *every* element of `Fix(a)` (`botFix_le`), so trivially below
any particular member of a (non-empty) directed family. -/
theorem isCompactFix_botFix (h : ClosureOperator a) : IsCompactFix h (botFix h) := by
  intro I _ d _ _
  obtain ⟨i0⟩ := (inferInstance : Nonempty I)
  exact ⟨i0, botFix_le h (d i0)⟩

end ClosureOperator

end DomainTheory.NeighbourhoodSystems
