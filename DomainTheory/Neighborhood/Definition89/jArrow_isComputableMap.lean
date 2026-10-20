/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88n
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Exercise326Sum
import DomainTheory.Neighborhood.Exercise319
import DomainTheory.Neighborhood.Definition89.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326
















theorem jArrow_isComputableMap :
    IsComputableMap UComputablePresentation funSpaceUUPresentation jArrow :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.2.2.2

end DomainTheory.Neighborhood
