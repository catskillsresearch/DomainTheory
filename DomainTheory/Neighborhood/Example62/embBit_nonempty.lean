/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Exercise319Sum
import DomainTheory.Neighborhood.Example62.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62













theorem embBit_nonempty {b : Bool} {X : Set Str} (hX : X.Nonempty) : (embBit b X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨b :: w', w', rfl, hw'⟩

end Example62
end DomainTheory.Neighborhood
