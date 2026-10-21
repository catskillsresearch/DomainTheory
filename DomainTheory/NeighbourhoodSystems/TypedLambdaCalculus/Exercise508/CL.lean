/-ai
A variable-free combinator expression is either a constant, given by an element of a domain, or an application of an expression of arrow type to an expression of the argument type. Its denotation sends a constant to that element and an application to the element map of the denotation of the function applied to the denotation of the argument.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Dom

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `CL A`: a **variable-free** combinator expression of type `A`. The only constructors are
constants and application, so application (`σ(τ)`) is the sole mode of combination. -/
inductive CL : Dom → Type 1 where
  | con {A : Dom} (c : A.sys.Element) : CL A
  | app {A B : Dom} (f : CL (A.arrow B)) (a : CL A) : CL B


/-- The denotation of a variable-free combinator expression: a single element. -/
def CL.denote : {A : Dom} → CL A → A.sys.Element
  | _, .con c => c
  | _, .app f a => (toApproxMap f.denote).toElementMap a.denote

end DomainTheory.NeighbourhoodSystems.Exercise508
