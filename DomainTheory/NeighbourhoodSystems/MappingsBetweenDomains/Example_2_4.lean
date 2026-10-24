module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_17

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example24
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

section
/- concordance: source L663 EXAMPLE 2.4 erase a run of ones -/
/-- **Example 2.4 — the run-eliminating mapping `g : B → B`.** `X g Y` iff `X = σΣ*` and the cone of
the guaranteed output `(out σ)Σ*` approximates `Y`. Definition 2.1: (i) `out [] = []` so `Δ g Δ`;
(ii) a fixed cone has a unique prefix, and the value is the principal filter `↑((out σ)Σ*)`, closed
under `∩`; (iii) `out_mono` shrinks the output cone as the input cone shrinks. -/
def runMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (out σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [out_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (out σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (out σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (out σ') ⊆ cone (out σ) := cone_subset_cone.mpr (out_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩
end

section
/-- **A leading `0` always emits it and continues copying.** `out([0]++τ) = 0::out τ`, for every
tail `τ`. (Exercise 2.17's first equation, at the token level.) -/
theorem out_append_false (τ : Str) : out ([false] ++ τ) = false :: out τ := rfl
end

section
/-- **`10` terminates the run and emits the `0`, whatever follows.** `out([1,0]++τ) = 0::τ`, for
every tail `τ`. (Exercise 2.17's third equation, at the token level.) -/
theorem out_append_trueFalse (τ : Str) : out ([true, false] ++ τ) = false :: τ := rfl
end

section
/-- **A second consecutive `1` changes nothing.** `out([1,1]++τ) = out([1]++τ)`: once inside the
run of `1`'s, an extra `1` is simply swallowed by `del`. (Exercise 2.17's second equation, at the
token level — the recursive step behind the uniqueness argument for `runMap`.) -/
theorem out_append_trueTrue (τ : Str) : out ([true, true] ++ τ) = out ([true] ++ τ) := rfl
end

section
/-- Cons-form restatement of `out_append_trueFalse`, for peeling one token at a time in `key`. -/
theorem out_true_false (t : Str) : out (true :: false :: t) = false :: t := rfl
end

section
/-- Cons-form restatement of `out_append_trueTrue`, for peeling one token at a time in `key`. -/
theorem out_true_true (t : Str) : out (true :: true :: t) = out (true :: t) := rfl
end

section
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
end

section
/-- **`runMap`'s relation on a cone, read off.** `σΣ* g Y ↔ Y ∈ B ∧ (out σ)Σ* ⊆ Y` — the defining
existential collapses since a cone has a *unique* generating prefix (`cone_injective`). -/
theorem runMap_rel_cone (σ : Str) (Y : Set Str) :
    runMap.rel (cone σ) Y ↔ B.mem Y ∧ cone (out σ) ⊆ Y := by
  constructor
  · rintro ⟨ρ, hρ, hYmem, hsub⟩
    obtain rfl : ρ = σ := (cone_injective hρ).symm
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩
end

end DomainTheory.NeighbourhoodSystems.Example24
