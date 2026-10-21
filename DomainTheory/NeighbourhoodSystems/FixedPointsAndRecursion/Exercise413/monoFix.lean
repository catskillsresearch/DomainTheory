/-ai
The least fixed point of an endomap f of the elements, relative to a witness a with f(a) below a, is the infimum of the set of pre-fixed points. Nonemptiness of that set is witnessed by a.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.preFix
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.mem_preFix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- **Exercise 4.13(1) (Scott 1981, PRG-19).** The least fixed point of a *monotone* `f` defined
purely as the greatest lower bound of the pre-fixed points, `⋂ {x ∣ f(x) ⊑ x}`. Well-defined as an
element by Exercise 1.18 (`sInf`); the non-emptiness witness is any `a` with `f(a) ⊑ a`. -/
def monoFix (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a) : V.Element :=
  V.sInf (preFix f) ⟨a, ha⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
