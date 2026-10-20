/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example43
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Theorem56.Basic


namespace DomainTheory.Neighborhood.Theorem56

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.Neighborhood.Exercise326 (cond)










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
end DomainTheory.Neighborhood.Theorem56
