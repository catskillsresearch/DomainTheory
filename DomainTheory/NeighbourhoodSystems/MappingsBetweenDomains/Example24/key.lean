/-ai
Any approximable self-map of the binary system that satisfies the four run equations agrees with the output scan on principal elements: its value at the principal element of a string is the principal element of the output of that string.

The argument recurses on the string. For the empty string the output is empty, so removing the empty shift leaves bottom on the right; monotonicity along bottom below the single one, the equation sending that element to bottom, and the leastness of bottom give equality. The singleton one has empty output and is that same equation. A one followed by a zero rewrites the output, splits off the two-token prefix, and applies the one-zero equation. Two leading ones rewrite the output, split off that prefix, apply the one-one equation, and recurse on the tail that still begins with one. A leading zero rewrites the output, splits off that token, applies the zero equation, and recurses on the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_true_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_true_false

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


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

end DomainTheory.NeighbourhoodSystems.Example24
