/-ai
The pair-indexed packing of a sequence of maps at x equals ⊤ if and only if every map in the sequence sends x to ⊤.

If the packing is ⊤, every pair code (n, m) lies in it, so every m lies in the nth value. Conversely, if every value is ⊤, every natural number is the code of some pair (n, m) with m in that value, so the packing is ⊤.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace
























theorem pairIndexed_eq_top (fs : ℕ → Pomega → Pomega) (x : Pomega) :
    pairIndexed fs x = topElem ↔ ∀ n, fs n x = topElem := by
  constructor
  · intro h n
    ext m
    constructor
    · intro _; trivial
    · intro _
      have : pair n m ∈ pairIndexed fs x := by rw [h]; exact Set.mem_univ _
      obtain ⟨n', m', heq, hm⟩ := this
      obtain ⟨rfl, rfl⟩ := pair_inj heq
      exact hm
  · intro h
    ext k
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨n, m, hk⟩ := exists_pair k
      exact ⟨n, m, hk.symm, by rw [h n]; exact Set.mem_univ m⟩

end DomainTheory.DataTypesAsLattices
