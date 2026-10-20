/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import DomainTheory.Neighborhood.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.Neighborhood.Exercise722.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap


































theorem powerLang_concat (w : List Bool) :
    concat (powerLang w) (powerLang w) ⊆ powerLang w := by
  rintro u ⟨a, ⟨m, hm⟩, b, ⟨n, hn⟩, rfl⟩
  exact ⟨m + n, by rw [repeatWord_add, hm, hn]⟩

end Exercise722
end DomainTheory.Neighborhood
