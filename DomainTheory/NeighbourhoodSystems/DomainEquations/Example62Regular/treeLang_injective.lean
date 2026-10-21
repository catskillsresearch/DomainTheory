/-ai
The language determines the tree: trees with the same language are equal.

If the languages agree, function extensionality compares the labels at a word. Membership of that word in the two languages agrees by rewriting the equality, and the membership law turns the agreement into an agreement of Boolean values. Splitting on the value of each tree at the word, simplification closes every case.
ai-/
module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}


/-- The label function recovers the tree from its language, so `treeLang` is **one-one**: two trees
with the same language are the same tree (a node's `±` label is recorded by whether its selector is
in the language). -/
theorem treeLang_injective : Function.Injective (treeLang (n := n)) := by
  intro a a' h
  funext σ
  have hmem : (σ ∈ treeLang a) ↔ (σ ∈ treeLang a') := by rw [h]
  simp only [mem_treeLang] at hmem
  cases ha : a σ <;> cases ha' : a' σ <;> simp_all

end Example62Regular
end DomainTheory.NeighbourhoodSystems
