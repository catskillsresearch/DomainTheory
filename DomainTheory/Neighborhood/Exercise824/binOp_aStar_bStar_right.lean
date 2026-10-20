/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise823
public import DomainTheory.Neighborhood.Exercise824.Basic
public import DomainTheory.Neighborhood.Exercise824.toElementMap_fixElement_snd

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}













/-- `(aStar s t, bStar s t)` is a *genuine* fixed point of the pair `(s, t)`. -/
theorem binOp_aStar_bStar_right (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    binOp t (aStar s t) (bStar s t) = bStar s t := by
  unfold binOp aStar bStar
  rw [toFilter_toApproxMap, toFilter_toApproxMap, pair_fst_snd, toElementMap_fixElement_snd]

end Exercise824
end DomainTheory.Neighborhood
