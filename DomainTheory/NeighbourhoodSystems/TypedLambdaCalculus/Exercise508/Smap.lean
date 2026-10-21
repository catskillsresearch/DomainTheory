/-ai
The combinator S, as an approximable map, is the double curry of its uncurried body. It sends a map from the domain into a function space to a map from a function space into a function space, so that S of F of G of x is F of x applied to G of x.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Dom
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Poly
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.CL
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Sbody

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `S = λf, g, x. f(x)(g(x))`, the curried form
`(𝒟ₓ → (𝒟ₐ → 𝒟_b)) → ((𝒟ₓ → 𝒟ₐ) → (𝒟ₓ → 𝒟_b))`. -/
def Smap (Vx : NeighborhoodSystem αx) (Va : NeighborhoodSystem αa) (Vb : NeighborhoodSystem αb) :
    ApproximableMap (funSpace Vx (funSpace Va Vb))
      (funSpace (funSpace Vx Va) (funSpace Vx Vb)) :=
  curry (curry (Sbody Vx Va Vb))

end DomainTheory.NeighbourhoodSystems.Exercise508
