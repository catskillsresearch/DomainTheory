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

/-- `K = λx, y.x` as an element of `(A → (X → A))`. -/
def Kelem (A X : Dom) : (A.arrow (X.arrow A)).sys.Element := toFilter (curry (proj₀ A.sys X.sys))

end DomainTheory.NeighbourhoodSystems.Exercise508
