/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Exercise216.Basic


namespace DomainTheory.Neighborhood.Exercise216

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB




/-- **The recursive core of uniqueness.** Any `g` satisfying the three equations agrees with
`parityMap` on every principal (finite) element `σ⊥`. Recursion peels *two* tokens at a time
(mirroring `scan`'s own recursion `scan(00τ)=scanτ`): `1τ` and `01τ` are pinned directly by
`hg.one`/`hg.zeroOne` for *any* tail (no recursion needed there); `00τ` reduces to `τ` by
`hg.zeroZero`, decreasing structurally. The base case `σ = []` and the leftover singleton
`σ = [false]` (an odd trailing zero, never reached by the two-at-a-time step) are the two places
genuine order theory enters: `⊥ ≤ 1⊥` and `⊥ ≤ 01⊥` force `g(⊥) ≤ true` and `g(⊥) ≤ false`, and
`⊥` is the *only* element below both (`eq_botElt_of_le`, `𝒯`'s flatness); the singleton then
follows by squeezing `g(0⊥)` between `⊥` and `g(00⊥) = g(⊥)` via monotonicity. -/
theorem key (g : ApproximableMap B Example23.T) (hg : SatisfiesParityEquations g) :
    ∀ σ : Str, g.toElementMap (sigmaElt σ B.bot) = Example23.valElt (Example23.scan σ)
  | [] => by
      rw [sigmaElt_nil]
      have h1 : g.toElementMap B.bot ≤ Example23.trueElt := by
        have hm := g.toElementMap_mono (B.bot_le (sigmaElt [true] B.bot))
        rwa [hg.one] at hm
      have h2 : g.toElementMap B.bot ≤ Example23.falseElt := by
        have hm := g.toElementMap_mono (B.bot_le (sigmaElt [false, true] B.bot))
        rwa [hg.zeroOne] at hm
      exact Example23.eq_botElt_of_le h1 h2
  | [false] => by
      have hbase : g.toElementMap B.bot = Example23.botElt := by
        have h0 := key g hg []
        rwa [sigmaElt_nil] at h0
      have hb : sigmaElt [false] B.bot ≤ sigmaElt [false, false] B.bot := by
        rw [sigmaElt_bot, sigmaElt_bot]
        exact (sigmaBot_le_iff _ _).mpr ⟨[false], rfl⟩
      have hm : g.toElementMap (sigmaElt [false] B.bot) ≤ Example23.botElt := by
        have := g.toElementMap_mono hb
        rwa [hg.zeroZero, hbase] at this
      have hm2 : Example23.botElt ≤ g.toElementMap (sigmaElt [false] B.bot) :=
        Example23.botElt_le _
      exact (le_antisymm hm hm2).trans rfl
  | (true :: t) => by
      rw [show (true :: t : Str) = [true] ++ t from rfl, sigmaElt_append, hg.one,
        Example23.scan_append_true]
      rfl
  | (false :: true :: t) => by
      rw [show (false :: true :: t : Str) = [false, true] ++ t from rfl, sigmaElt_append,
        hg.zeroOne, Example23.scan_append_falseTrue]
      rfl
  | (false :: false :: t) => by
      rw [show (false :: false :: t : Str) = [false, false] ++ t from rfl, sigmaElt_append,
        hg.zeroZero, key g hg t, Example23.scan_append_falseFalse]

end DomainTheory.Neighborhood.Exercise216
