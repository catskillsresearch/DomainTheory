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

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


variable {α β γ : Type*}


variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}


/-- The defining equation of `S`: `S(F)(G)(x) = F(x)(G(x))`. -/
theorem Smap_apply (F : (funSpace Vx (funSpace Va Vb)).Element) (G : (funSpace Vx Va).Element)
    (x : Vx.Element) :
    (toApproxMap ((toApproxMap ((Smap Vx Va Vb).toElementMap F)).toElementMap G)).toElementMap x
      = (toApproxMap ((toApproxMap F).toElementMap x)).toElementMap ((toApproxMap G).toElementMap x) := by
  rw [Smap, toElementMap_curry_apply, toElementMap_curry_apply]
  simp only [Sbody, toElementMap_comp, toElementMap_paired, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

end DomainTheory.NeighbourhoodSystems.Exercise508
