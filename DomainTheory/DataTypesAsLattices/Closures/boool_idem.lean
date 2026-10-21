/-ai
The conditional set obtained by testing membership of zero and of a successor, with branches the singleton zero and the successor of the full set, is idempotent.

The argument splits on whether zero lies in u and whether some successor does. If both do, the inner conditional is the full set, and the outer conditional of the full set is again the full set. If only zero lies in u, the inner conditional is the singleton zero, and the outer conditional of that singleton is itself. If only a successor lies in u, the inner conditional is the successor of the full set; zero is absent from it and one is present, so the outer conditional stays that successor set. If neither lies in u, the inner conditional is empty, and the outer conditional of the empty set is empty.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


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
