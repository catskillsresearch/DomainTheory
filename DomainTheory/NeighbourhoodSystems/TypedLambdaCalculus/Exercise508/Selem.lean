module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Dom
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Poly
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.CL
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Smap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `S = λf, g, x. f(x)(g(x))` as an element of
`((X → (A → B)) → ((X → A) → (X → B)))`. -/
def Selem (X A B : Dom) :
    ((X.arrow (A.arrow B)).arrow ((X.arrow A).arrow (X.arrow B))).sys.Element :=
  toFilter (Smap X.sys A.sys B.sys)

end DomainTheory.NeighbourhoodSystems.Exercise508
