/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Exercise823
import DomainTheory.Neighborhood.Exercise715
import DomainTheory.Neighborhood.Exercise825Pow
import DomainTheory.Neighborhood.Exercise825Embed
import DomainTheory.Neighborhood.Exercise825Closing
import DomainTheory.Neighborhood.Exercise820
import DomainTheory.Neighborhood.Exercise825FixedPoint.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap












theorem toElementMap_RMap (c : ApproximableMap U U) (ψ φ : (funSpace U U).Element) (x : U.Element) :
    (RMap c).toElementMap (pair ψ (pair φ x)) =
      c.toElementMap ((toApproxMap φ).toElementMap ((toApproxMap ψ).toElementMap x)) := by
  simp only [RMap, toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end DomainTheory.Neighborhood
