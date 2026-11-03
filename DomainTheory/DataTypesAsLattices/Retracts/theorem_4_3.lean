module

public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more
import DomainTheory.DataTypesAsLattices.Retracts.typed_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

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
  ⟨arrowR.isRetract ha hb, arrowR.isStrict, fun _ => typed.arrowR_iff ha hb,
    arrowR.mono, fun _ _ => arrowR.functor,
    fun _ _ hf hf' => typed.comp ha hb hc hf hf'⟩

end DomainTheory.DataTypesAsLattices
