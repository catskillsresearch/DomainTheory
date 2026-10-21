/-ai
An endofunctor on domains is monotone on domains when every subsystem relation carries pointwise monotonicity data for the images and their projection pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.MonotoneAt

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe w

/-- **Definition 6.13 (Scott 1981, PRG-19), monotone on domains.** A functor `T` is *monotone on
domains* iff every subdomain relation `D ◁ E` is carried to a subdomain relation `T(D) ◁ T(E)` whose
projection pair is `(T(i), T(j))` — see `MonotoneAt`. -/
def MonotoneOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∀ {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E), MonotoneAt T h

end DomainTheory.NeighbourhoodSystems
