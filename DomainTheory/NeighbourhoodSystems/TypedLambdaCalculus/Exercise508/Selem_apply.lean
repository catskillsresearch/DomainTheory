module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Dom
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Poly
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.CL
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Sbody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Smap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Ielem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Kelem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Selem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.bracket
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.toApproxMap_toFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Smap_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


variable {α β γ : Type*}


variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}


/-- `S(F)(G)(x) = F(x)(G(x))`. -/
theorem Selem_apply (X A B : Dom)
    (F : (X.arrow (A.arrow B)).sys.Element) (G : (X.arrow A).sys.Element) (x : X.sys.Element) :
    (toApproxMap ((toApproxMap ((toApproxMap (Selem X A B)).toElementMap F)).toElementMap G)).toElementMap x
      = (toApproxMap ((toApproxMap F).toElementMap x)).toElementMap ((toApproxMap G).toElementMap x) := by
  rw [Selem, toApproxMap_toFilter]
  exact Smap_apply F G x

end DomainTheory.NeighbourhoodSystems.Exercise508
