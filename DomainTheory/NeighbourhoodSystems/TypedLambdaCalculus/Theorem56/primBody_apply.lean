module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)










section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)


theorem primBody_apply (k : (funSpace (prod N N) N).Element) (x y : N.Element) :
    (primBody f g).toElementMap (pair k (pair x y)) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap x)
          (pair (f.toElementMap y)
            (g.toElementMap
              (pair (predMap.toElementMap x)
                (pair y ((toApproxMap k).toElementMap
                  (pair (predMap.toElementMap x) y))))))) := by
  rw [primBody, toElementMap_comp]
  simp only [argX, argY, kSel, qSel, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

end PrimRec
end DomainTheory.NeighbourhoodSystems.Theorem56
