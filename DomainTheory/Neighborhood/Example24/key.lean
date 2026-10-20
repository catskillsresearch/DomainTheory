/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example24.Basic
import DomainTheory.Neighborhood.Example24.out_true_true
import DomainTheory.Neighborhood.Example24.out_true_false


namespace DomainTheory.Neighborhood.Example24

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB












/-- **The recursive core of uniqueness.** Any `g` satisfying the four equations agrees with
`runMap` on every principal (finite) element `σ⊥`. The recursion peels *one* token at a time,
matching `out`'s own case split: a leading `0` recurses via `hg.zero` (`Basic decreasing case`);
inside a run of `1`'s, a further `1` recurses via `hg.oneOne` (peeling to `1τ`, still one token
shorter); a `1` followed by `0` is pinned *directly* by `hg.oneZero` for any tail (no recursion);
the lone token `1` (nothing more) is pinned directly by `hg.one`; and the base case `σ = []` is
the one place order theory enters: `⊥ ≤ 1⊥` forces `g(⊥) ≤ g(1⊥) = ⊥` by monotonicity, and `⊥` is
already the least element, so `g(⊥) = ⊥`. -/
theorem key (g : ApproximableMap B B) (hg : SatisfiesRunEquations g) :
    ∀ σ : Str, g.toElementMap (sigmaElt σ B.bot) = sigmaElt (out σ) B.bot
  | [] => by
      rw [show out ([] : Str) = ([] : Str) from rfl, sigmaElt_nil]
      have hm := g.toElementMap_mono (B.bot_le (sigmaElt [true] B.bot))
      rw [hg.one] at hm
      exact le_antisymm hm (B.bot_le _)
  | [true] => by
      rw [show out [true] = ([] : Str) from rfl, sigmaElt_nil]
      exact hg.one
  | true :: false :: t => by
      rw [out_true_false, show (true :: false :: t : Str) = [true, false] ++ t from rfl,
        sigmaElt_append, hg.oneZero, ← sigmaElt_append]
      rfl
  | true :: true :: t => by
      rw [out_true_true, show (true :: true :: t : Str) = [true, true] ++ t from rfl,
        sigmaElt_append, hg.oneOne, ← sigmaElt_append]
      exact key g hg (true :: t)
  | false :: t => by
      rw [out_false, show (false :: t : Str) = [false] ++ t from rfl, sigmaElt_append, hg.zero,
        key g hg t, show (false :: out t : Str) = [false] ++ out t from rfl, sigmaElt_append]

end DomainTheory.Neighborhood.Example24
