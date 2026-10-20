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
import DomainTheory.Neighborhood.Exercise825FixedPoint.Dsol_isomorphic_funSpace_cCombinator
import DomainTheory.Neighborhood.Exercise825FixedPoint.hVV_cCombinator


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap



















/-- **Exercise 8.25 (Scott 1981, PRG-19), main theorem.** `D ≅ D → D`, for
`D := fixedNbhd (fixOp (tOpMap cCombinator))`: a non-trivial domain isomorphic to its own function
space (see `U_trianglelefteq_Dsol` below for non-triviality). -/
theorem exercise_8_25_main :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)))
        (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) :=
  funSpace_self_isomorphic Dsol_isomorphic_funSpace_cCombinator hVV_cCombinator

end DomainTheory.Neighborhood
