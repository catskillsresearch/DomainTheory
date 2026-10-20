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
import DomainTheory.Neighborhood.Exercise825FixedPoint.isProjection_cCombinator
import DomainTheory.Neighborhood.Exercise825FixedPoint.isFinitary_cCombinator


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap








theorem isFinitaryProjection_cCombinator : IsFinitaryProjection cCombinator :=
  ⟨isProjection_cCombinator, isFinitary_cCombinator⟩

end DomainTheory.Neighborhood
