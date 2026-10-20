/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise118
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.Exercise413.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem





/-- `monoFix f ha ⊑ x` for every pre-fixed point `x` (`f(x) ⊑ x`). -/
theorem monoFix_le_preFix (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a)
    {x : V.Element} (hx : f x ≤ x) : monoFix f ha ≤ x :=
  V.sInf_le (preFix f) ⟨a, ha⟩ hx

end NeighborhoodSystem
end DomainTheory.Neighborhood
