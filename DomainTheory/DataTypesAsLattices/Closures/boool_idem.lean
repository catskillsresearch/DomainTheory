module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Isolated
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor
public import DomainTheory.DataTypesAsLattices.Closures.boxTag
public import DomainTheory.DataTypesAsLattices.Closures.Vapply
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.Vstep
public import DomainTheory.DataTypesAsLattices.Closures.VapplyY
public import DomainTheory.DataTypesAsLattices.Closures.closureRangeCountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.Closures.representClosure
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode
public import DomainTheory.DataTypesAsLattices.Closures.representationOrderIso
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.selfArrowStep
public import DomainTheory.DataTypesAsLattices.Closures.dEq
public import DomainTheory.DataTypesAsLattices.Closures.boool
public import DomainTheory.DataTypesAsLattices.Closures.closure_expansive
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact_isCompact
public import DomainTheory.DataTypesAsLattices.Closures.compact_fixed_iff
public import DomainTheory.DataTypesAsLattices.Closures.retractBasis_eq_compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.fixed_eq_sSup_compacts
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_mono
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode_app
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode_encode
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode_fixed

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
