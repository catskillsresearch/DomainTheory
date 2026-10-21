/-ai
Scott 1976, Theorem 4.5, the sum theorem. If a and b are retracts, then a ⊕ b is a retract and is strict, and an element lies in its range if and only if it is bottom, or top, or a sequence pair of the numeral 0 with an element of the range of a, or a sequence pair of the numeral 1 with an element of the range of b.

The three conjuncts are the retract lemma for the sum, the strictness lemma for the sum, and the range characterization of the sum.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isStrict
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_iff

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















/-- **Scott 1976, Theorem 4.5 (The sum theorem).** -/
theorem theorem_4_5_sum {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (plusR a b) ∧ IsStrict (plusR a b) ∧
      (∀ u, typed u (plusR a b) ↔
        u = botElem ∨ u = topElem ∨
          (∃ x, u = pairSeq (ofNat 0) x ∧ typed x a) ∨
            (∃ y, u = pairSeq (ofNat 1) y ∧ typed y b)) :=
  ⟨plusR_isRetract ha hb, plusR_isStrict a b, fun _u => plusR_typed_iff ha hb⟩

end DomainTheory.DataTypesAsLattices
