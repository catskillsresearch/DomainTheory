/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition68
import DomainTheory.Neighborhood.Proposition611
import DomainTheory.Neighborhood.Proposition612
import DomainTheory.Neighborhood.Definition613.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe w




/-- The **identity functor is monotone on domains**: it fixes objects and maps, so `T(D) ◁ T(E)` is
just `D ◁ E` and the projection pair is unchanged. -/
theorem monotoneOnDomains_id : MonotoneOnDomains (idEndofunctor DomainObj.{w}) := by
  intro α D E h
  exact ⟨rfl, h, HEq.rfl, HEq.rfl⟩

end DomainTheory.Neighborhood
