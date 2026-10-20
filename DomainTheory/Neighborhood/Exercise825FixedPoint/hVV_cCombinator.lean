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
import DomainTheory.Neighborhood.Exercise825FixedPoint.fixedNbhd_cCombinator_isomorphic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap



















/-- **`fixedNbhd c × fixedNbhd c ≅ fixedNbhd c`**, transported from `Exercise825Pow.pow_prod_isomorphic`
along `fixedNbhd_cCombinator_isomorphic`. -/
theorem hVV_cCombinator :
    prod (fixedNbhd cCombinator) (fixedNbhd cCombinator) ≅ᴰ fixedNbhd cCombinator :=
  ((fixedNbhd_cCombinator_isomorphic.prod fixedNbhd_cCombinator_isomorphic).trans
    (pow_prod_isomorphic U)).trans fixedNbhd_cCombinator_isomorphic.symm

end DomainTheory.Neighborhood
