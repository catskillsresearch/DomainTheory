module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.toApproxMap_toFilter

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


variable {α β γ : Type*}


variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}


/-- `K(c)(x) = c`. -/
theorem Kelem_apply (A X : Dom) (c : A.sys.Element) (x : X.sys.Element) :
    (toApproxMap ((toApproxMap (Kelem A X)).toElementMap c)).toElementMap x = c := by
  rw [Kelem, toApproxMap_toFilter]
  have h := toElementMap_curry_apply (proj₀ A.sys X.sys) c x
  rw [toElementMap_proj₀, fst_pair] at h
  exact h

end DomainTheory.NeighbourhoodSystems.Exercise508
