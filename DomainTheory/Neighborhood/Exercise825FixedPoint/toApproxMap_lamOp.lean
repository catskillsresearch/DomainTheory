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
import DomainTheory.Neighborhood.Exercise825FixedPoint.toElementMap_RMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap















/-- **`lamOp c` recovers `expMap (-) c = lamComb (-) c` at every `a`.** The heart of the
continuity argument: unwinding both curry layers (`curryC_toApproxMap`, `toElementMap_curry_apply`
twice) and `RMap`'s value formula (`toElementMap_RMap`) against `expMap`'s own value formula
(`toApproxMap_toElementMap_expMap`) shows both sides send `φ` to (the element representing)
`x ↦ c(φ(a(x)))`. -/
theorem toApproxMap_lamOp (c a : ApproximableMap U U) :
    toApproxMap ((lamOp c).toElementMap (toFilter a)) = expMap a c := by
  apply ApproximableMap.ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ApproximableMap.ext_of_toElementMap
  intro x
  show (toApproxMap ((toApproxMap ((lamOp c).toElementMap (toFilter a))).toElementMap φ)).toElementMap x
    = (toApproxMap ((expMap a c).toElementMap φ)).toElementMap x
  rw [lamOp, toElementMap_comp, curryC_toApproxMap, toElementMap_curry_apply, curryOnceC,
    toElementMap_curry_apply, toElementMap_RMap, Sub8_6.toApproxMap_toFilter,
    toApproxMap_toElementMap_expMap, toElementMap_comp, toElementMap_comp]

end DomainTheory.Neighborhood
