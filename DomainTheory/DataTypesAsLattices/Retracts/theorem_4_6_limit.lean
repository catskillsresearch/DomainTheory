/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_6


namespace DomainTheory.DataTypesAsLattices







































































/-- **Scott 1976, Theorem 4.6**, inverse-limit half packaged with the
retract half. Under the paper's extra strictness and `⊑`-monotonicity
hypotheses, the range of `Y(F)` is order-isomorphic to the inverse
limit of the ranges of `Fⁿ(⊥)`. Stated without `≃o` so the compared
type does not mention a `CompleteLattice` instance. -/
theorem theorem_4_6_limit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    (∀ n, IsRetract (iterateBot F n)) ∧
      IsRetract (funOf Ycomb (graph F)) ∧
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
