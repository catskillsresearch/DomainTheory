/-ai
The difference automaton accepts a word if and only if the word lies in the language of the first expression and outside the language of the second.

If the automaton accepts the word, its evaluation is the singleton of the pair of finite evaluations, so that pair is accepting: the first component meets its accept set and the second is disjoint from its accept set. The first fact is membership in the first language, and membership in the second language would make the second intersection nonempty. Conversely, the pair of finite evaluations is accepting because membership in the first language makes the first intersection nonempty and failure of membership in the second language forces the second intersection to be empty, and evaluation returns exactly that singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.denote_iff_evalFin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.diffNFA_eval

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set


/-- **`diffNFA` accepts exactly `denote e₁ \ denote e₂`.** -/
theorem diffNFA_mem_accepts_iff (e1 e2 : SExpr) (w : List Bool) :
    w ∈ (diffNFA e1 e2).accepts ↔ w ∈ denote e1 ∧ w ∉ denote e2 := by
  constructor
  · rintro ⟨s, hs, hse⟩
    rw [diffNFA_eval, Set.mem_singleton_iff] at hse
    subst hse
    obtain ⟨hacc1, hacc2⟩ := hs
    refine ⟨(denote_iff_evalFin e1 w).mpr hacc1, fun hmem => ?_⟩
    rw [denote_iff_evalFin] at hmem
    rw [hacc2] at hmem
    exact Finset.not_nonempty_empty hmem
  · rintro ⟨h1, h2⟩
    refine ⟨(evalFin e1 w, evalFin e2 w), ⟨(denote_iff_evalFin e1 w).mp h1, ?_⟩, ?_⟩
    · show evalFin e2 w ∩ acceptFin e2 = ∅
      by_contra hcontra
      exact h2 ((denote_iff_evalFin e2 w).mpr (Finset.nonempty_iff_ne_empty.mpr hcontra))
    · rw [diffNFA_eval]; rfl

end Exercise722
end DomainTheory.NeighbourhoodSystems
