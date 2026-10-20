/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem86
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.Exercise315
public import DomainTheory.Neighborhood.Exercise816
public import DomainTheory.Neighborhood.Exercise823.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}







theorem tOp_toApproxMap (t : ApproximableMap (funSpace E E) (funSpace E E))
    (φ : (funSpace E E).Element) : tOp t (toApproxMap φ) = toApproxMap (t.toElementMap φ) := by
  unfold tOp
  rw [toFilter_toApproxMap]

end Exercise823
end DomainTheory.Neighborhood
