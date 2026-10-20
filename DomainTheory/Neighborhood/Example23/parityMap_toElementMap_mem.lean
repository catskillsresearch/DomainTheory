/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.Example12
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example23.Basic
import DomainTheory.Neighborhood.Example23.parityMap_rel_cone


namespace DomainTheory.Neighborhood.Example23

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB












/-- **`parityMap`'s elementwise value, read off cone-by-cone.** `f(x).mem Y` iff *some* cone
`σΣ* ∈ x` already witnesses `Y ∈ valElt(scan σ)` — every neighbourhood of `x` is a cone
(`Element.sub`), and `parityMap`'s relation is exactly `parityMap_rel_cone`. -/
theorem parityMap_toElementMap_mem (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ (valElt (scan τ)).mem Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (parityMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone τ, hτ, (parityMap_rel_cone τ Y).mpr hval⟩

end DomainTheory.Neighborhood.Example23
