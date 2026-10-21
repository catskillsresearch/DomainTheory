/-ai
The uncurried body of the combinator S sends a nested pair consisting of maps F and G and an element x to the application of F at x to G at x. It is evaluation composed with the pairing of two further evaluations, one applying the first projection of the outer pair to the second component and the other applying the second projection of the outer pair to the second component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Dom
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Poly
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.CL

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- The uncurried body of `S`: with `F : 𝒟ₓ → (𝒟ₐ → 𝒟_b)`, `G : 𝒟ₓ → 𝒟ₐ`, `x : 𝒟ₓ`,
`Sbody⟨⟨F, G⟩, x⟩ = (F x)(G x)`, expressed using only `proj`, `pair` and `eval`. -/
def Sbody (Vx : NeighborhoodSystem αx) (Va : NeighborhoodSystem αa) (Vb : NeighborhoodSystem αb) :
    ApproximableMap
      (prod (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx) Vb :=
  (evalMap Va Vb).comp
    (paired
      ((evalMap Vx (funSpace Va Vb)).comp
        (paired
          ((proj₀ (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)).comp
            (proj₀ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))
          (proj₁ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx)))
      ((evalMap Vx Va).comp
        (paired
          ((proj₁ (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)).comp
            (proj₀ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))
          (proj₁ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))))

end DomainTheory.NeighbourhoodSystems.Exercise508
