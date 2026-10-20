/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic
public import DomainTheory.Neighborhood.Exercise722Regular.Basic
public import DomainTheory.Neighborhood.Exercise722Regular.mem_denote_sigma

@[expose] public section


namespace DomainTheory.Neighborhood

namespace Exercise722


















/-- **The emptiness decider cannot decide relation (i).** `Σ ≠ "contains 0"`, witnessed by `[1] ∈ Σ`
but `[1] ∉ Σ·{0}·Σ`. To *decide* this inequality one must detect a word in `Σ ∩ ("contains 0")ᶜ` —
i.e. in the complement language `{1}*` — but `{1}*` is **not** expressible in the fragment (no
complement, no star other than the full `Σ`). Hence no fragment-emptiness query exposes the
difference: deciding equivalence needs machinery (a product/complement DFA, or a derivative
bisimulation) that goes strictly beyond emptiness of fragment expressions. -/
theorem sigma_ne_containsZero : denote .sigma ≠ denote containsZero := by
  intro h
  have h1 : ([true] : List Bool) ∈ denote .sigma := mem_denote_sigma _
  rw [h] at h1
  exact absurd h1 (by decide)

end Exercise722
end DomainTheory.Neighborhood
