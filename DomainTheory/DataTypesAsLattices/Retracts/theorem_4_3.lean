/-ai
Scott 1976, Theorem 4.3, the function space theorem. For retracts a, b, a', b', and c, the function space a ∘→ b is a retract; it is strict whenever b is strict; a set is typed by the function space exactly when it equals its composite with a and sends a-typed sets to b-typed sets; the function-space construction preserves the retract order; the function space of two typed maps is typed by the corresponding function space of function spaces; and the composite of typed maps is typed by the function space from a to c.

The six claims are the retract, strictness, typing, retract-order, functor, and composition lemmas for function spaces.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_isRetract
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_isStrict
public import DomainTheory.DataTypesAsLattices.Retracts.typed_arrowR_iff
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_functor
public import DomainTheory.DataTypesAsLattices.Retracts.typed_comp

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.3 (The function space theorem).** -/
theorem theorem_4_3 {a b a' b' c : Pomega}
    (ha : Retract a) (hb : Retract b) (_ha' : Retract a')
    (_hb' : Retract b') (hc : Retract c) :
    Retract (arrowR a b) ∧
      (IsStrict b → IsStrict (arrowR a b)) ∧
      (∀ u, typed u (arrowR a b) ↔
        u = comp u a ∧ ∀ x, typed x a → typed (funOf u x) b) ∧
      (retractLe a a' → retractLe b b' →
        retractLe (arrowR a b) (arrowR a' b')) ∧
      (∀ f f', typed f (arrowR a b) → typed f' (arrowR a' b') →
        typed (arrowR f f') (arrowR (arrowR b a') (arrowR a b'))) ∧
      (∀ f f', typed f (arrowR a b) → typed f' (arrowR b c) →
        typed (comp f' f) (arrowR a c)) :=
  ⟨arrowR_isRetract ha hb, arrowR_isStrict, fun _ => typed_arrowR_iff ha hb,
    arrowR_retractLe, fun _ _ => arrowR_functor,
    fun _ _ hf hf' => typed_comp ha hb hc hf hf'⟩

end DomainTheory.DataTypesAsLattices
