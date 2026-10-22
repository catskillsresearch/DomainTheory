
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_2_i_iso
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_2_ii
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_2_iii_exact
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_2_iv

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 7.2 (The isomorphism theorem).** -/
theorem theorem_7_2 {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    (∀ x y, funOf a x = funOf a y ↔ (Ea a).rel (funOf a x) (funOf a y)) ∧
      (∀ f g, (typed f (arrowR a b) → (arrowE (Ea a) (Ea b)).mem f) ∧
        ((arrowE (Ea a) (Ea b)).rel f g →
          (Ea (arrowR a b)).rel (funOf (arrowR a b) f)
            (funOf (arrowR a b) g)) ∧
        ((Ea (arrowR a b)).rel f g → (arrowE (Ea a) (Ea b)).rel f g)) ∧
      (∀ u v, (Ea (tensorR a b)).rel u v ↔ (prodE (Ea a) (Ea b)).rel u v) ∧
      (∀ u v, (Ea (plusR a b)).rel u v ↔
        (sumE (Ea a) (Ea b)).rel u v ∨
          (u = botElem ∧ v = botElem) ∨ (u = topElem ∧ v = topElem)) :=
  ⟨fun x y => theorem_7_2_i_iso ha x y,
    fun f g => theorem_7_2_ii ha hb f g,
    theorem_7_2_iii_exact a b,
    theorem_7_2_iv ha hb⟩

end DomainTheory.DataTypesAsLattices
