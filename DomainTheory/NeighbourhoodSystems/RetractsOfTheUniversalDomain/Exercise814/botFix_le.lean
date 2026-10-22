module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.botFix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section ClosureOperator

variable {a : ApproximableMap E E}

/-- **`a(⊥)` is the least element of `Fix(a)`**: `a(⊥) ⊑ y` for every `y ∈ Fix(a)`. Since `⊥ ⊑ y`
always, monotonicity gives `a(⊥) ⊑ a(y) = y`. -/
theorem botFix_le (h : ClosureOperator a) (y : FixSet a) : (botFix h).1 ≤ y.1 := by
  have h1 : a.toElementMap ⊥ ≤ a.toElementMap y.1 := a.toElementMap_mono bot_le
  rwa [y.2] at h1

end ClosureOperator

end DomainTheory.NeighbourhoodSystems
