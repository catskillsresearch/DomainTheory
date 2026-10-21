/-ai
A domain is a token type equipped with a neighbourhood system on that type. The arrow of two domains is the domain whose carrier is the type of approximable maps between their systems and whose system is the function space of those systems.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- A *domain*: a token type together with its neighbourhood system. Bundling lets us build an
intrinsically-typed syntax of combinator terms. We work over `Type` (universe `0`), which covers all
the concrete domains of these lectures (`N`, `T`, `C`, …) and their products/function spaces. -/
structure Dom where
  /-- The token type. -/
  carrier : Type
  /-- The neighbourhood system on `carrier`. -/
  sys : NeighborhoodSystem carrier

/-- The function domain `(A → B)`; its carrier is `ApproximableMap A.sys B.sys` and its system is the
function space `funSpace A.sys B.sys`. -/
abbrev Dom.arrow (A B : Dom) : Dom := ⟨ApproximableMap A.sys B.sys, funSpace A.sys B.sys⟩

end DomainTheory.NeighbourhoodSystems.Exercise508
