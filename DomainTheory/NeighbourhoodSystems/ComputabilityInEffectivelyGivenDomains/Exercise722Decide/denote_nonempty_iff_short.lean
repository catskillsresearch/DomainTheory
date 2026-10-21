/-ai
The language of e is nonempty if and only if some word in the list bounded by autStateCard e is accepted by the matcher.

The bound autStateCard e equals the number of automaton states. If the language is nonempty, acceptance by the automaton and the short accepted-word lemma give a word shorter than that number of states; arithmetic places it in the bounded list, and the matcher criterion accepts it. Conversely, the length bound is rewritten and the matcher criterion places the matched word in the language.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autStateCard
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.toNFA_accepts
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.exists_accepted_word_short
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autStateCard_eq_card

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

variable {σ : Type}

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

theorem denote_nonempty_iff_short (e : SExpr) :
    (denote e).Nonempty ↔ ∃ w ∈ wordsUpTo (autStateCard e), matchesB e w = true := by
  have hc : autStateCard e = Fintype.card (autState e) := autStateCard_eq_card e
  constructor
  · intro hne
    rw [← toNFA_accepts e] at hne
    obtain ⟨w, hwlt, hw⟩ := exists_accepted_word_short hne
    refine ⟨w, ?_, ?_⟩
    · rw [mem_wordsUpTo, hc]; omega
    · rw [matchesB_iff, ← toNFA_accepts e]; exact hw
  · intro ⟨w, hwmem, hmatch⟩
    rw [mem_wordsUpTo, hc] at hwmem
    exact ⟨w, (matchesB_iff e w).mp hmatch⟩

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems
