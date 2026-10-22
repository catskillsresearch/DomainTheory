module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_6

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.6**, inverse-limit half packaged with the
retract half. Under the paper's extra strictness and `⊑`-monotonicity
hypotheses, the range of `Y(F)` is order-isomorphic to the inverse
limit of the ranges of `Fⁿ(⊥)`. Stated without `≃o` so the compared
type does not mention a `CompleteLattice` instance. -/
theorem theorem_4_6_limit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    (∀ n, Retract (iterateBot F n)) ∧
      Retract (funOf Ycomb (graph F)) ∧
        ∃ φ : Fixpoints (funOf (fix F)) → RetractInverseLimit F,
          Function.Bijective φ ∧
            ∀ x y : Fixpoints (funOf (fix F)),
              (x : Pomega) ⊆ (y : Pomega) ↔
                ∀ n, (φ x).1 n ⊆ (φ y).1 n := by
  refine ⟨(theorem_4_6 hf hret).1, (theorem_4_6 hf hret).2, ?_⟩
  let iso := theorem_4_6_inverseLimit hf hret hstrict hmono
  refine ⟨iso, iso.bijective, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy n
    exact funOf_monotone_right (iterateBot F n) hxy
  · intro h
    have hx : (x : Pomega) = ⋃ n, funOf (iterateBot F n) (x : Pomega) := by
      calc
        (x : Pomega) = funOf (fix F) (x : Pomega) := x.property.symm
        _ = ⋃ n, funOf (iterateBot F n) (x : Pomega) := by
          change funOf (⋃ n, iterateBot F n) (x : Pomega) = _
          rw [funOf_iUnion]
    have hy : (y : Pomega) = ⋃ n, funOf (iterateBot F n) (y : Pomega) := by
      calc
        (y : Pomega) = funOf (fix F) (y : Pomega) := y.property.symm
        _ = ⋃ n, funOf (iterateBot F n) (y : Pomega) := by
          change funOf (⋃ n, iterateBot F n) (y : Pomega) = _
          rw [funOf_iUnion]
    change ∀ n, funOf (iterateBot F n) (x : Pomega) ⊆
      funOf (iterateBot F n) (y : Pomega) at h
    rw [hx, hy]
    intro k hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, h n hn⟩

end DomainTheory.DataTypesAsLattices
