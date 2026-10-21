/-ai
A retraction acts idempotently on elements: applying it twice returns the same element as applying it once.

Rewrite the double application as the composite, and use the retraction equation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- `a ∘ a = a` unwound at the element level: `a(a(x)) = a(x)` for every `x`. -/
theorem toElementMap_idem_of_isRetraction {a : ApproximableMap E E} (ha : IsRetraction a)
    (x : E.Element) : a.toElementMap (a.toElementMap x) = a.toElementMap x := by
  rw [← toElementMap_comp, ha]

end DomainTheory.NeighbourhoodSystems
