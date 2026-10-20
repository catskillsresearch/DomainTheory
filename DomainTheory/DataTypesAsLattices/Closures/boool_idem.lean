/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices



































theorem boool_idem (u : Pomega) :
    condSet (condSet u (ofNat 0) (succSet topElem)) (ofNat 0) (succSet topElem) =
      condSet u (ofNat 0) (succSet topElem) := by
  by_cases h0 : 0 ∈ u
  · by_cases hp : ∃ k, k + 1 ∈ u
    · have hcu : condSet u (ofNat 0) (succSet topElem) = topElem := by
        ext n
        constructor
        · intro _; exact Set.mem_univ n
        · intro _
          cases n with
          | zero => exact Or.inl ⟨rfl, h0⟩
          | succ n => exact Or.inr ⟨⟨n, Set.mem_univ n, rfl⟩, hp⟩
      rw [hcu]
      ext n
      constructor
      · intro _; exact Set.mem_univ n
      · intro _
        cases n with
        | zero => exact Or.inl ⟨rfl, Set.mem_univ 0⟩
        | succ n =>
          exact Or.inr ⟨⟨n, Set.mem_univ n, rfl⟩, ⟨0, Set.mem_univ 1⟩⟩
    · have hcu : condSet u (ofNat 0) (succSet topElem) = ofNat 0 := by
        ext n
        constructor
        · intro hn
          rcases hn with ⟨hn, _⟩ | ⟨_, ht⟩
          · exact hn
          · exact (hp ht).elim
        · intro hn
          exact Or.inl ⟨hn, h0⟩
      rw [hcu]
      ext n
      constructor
      · intro hn
        rcases hn with ⟨hn, _⟩ | ⟨_, ⟨k, hk⟩⟩
        · exact hn
        · simp [ofNat] at hk
      · intro hn
        exact Or.inl ⟨hn, rfl⟩
  · by_cases hp : ∃ k, k + 1 ∈ u
    · have hcu : condSet u (ofNat 0) (succSet topElem) = succSet topElem := by
        ext n
        constructor
        · intro hn
          rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
          · exact (h0 hz).elim
          · exact hy
        · intro hy
          exact Or.inr ⟨hy, hp⟩
      rw [hcu]
      have h0' : 0 ∉ succSet topElem := by
        intro ⟨n, _, hn⟩
        omega
      have hp' : ∃ k, k + 1 ∈ succSet topElem :=
        ⟨0, ⟨0, Set.mem_univ 0, rfl⟩⟩
      ext n
      constructor
      · intro hn
        rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
        · exact (h0' hz).elim
        · exact hy
      · intro hy
        exact Or.inr ⟨hy, hp'⟩
    · have hcu : condSet u (ofNat 0) (succSet topElem) = botElem := by
        ext n
        constructor
        · intro hn
          rcases hn with ⟨_, hz⟩ | ⟨_, ht⟩
          · exact (h0 hz).elim
          · exact (hp ht).elim
        · intro hn
          simp [botElem] at hn
      rw [hcu]
      ext n
      simp [condSet, botElem]

end DomainTheory.DataTypesAsLattices
