/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.isFinitaryProjection_aStar_bStar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.binOp_aStar_bStar_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.binOp_aStar_bStar_right

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}













/-- **Exercise 8.24, Claim 2 (the domain equations).** Given any correspondences `S, T` (bundling,
for each pair of maps, a type and a domain over it) with `Fix(binOp s a b) ≅ S(a,b)` and
`Fix(binOp t a b) ≅ T(a,b)` for every pair of finitary projections `a, b` (Scott's hypotheses
`D_{s(a,b)} ≅ S(D_a,D_b)`, `D_{t(a,b)} ≅ T(D_a,D_b)`), substituting the *exact* simultaneous fixed
point `a := aStar s t`, `b := bStar s t` and using `binOp_aStar_bStar_left/right` gives
`Fix(aStar s t) ≅ S(aStar s t, bStar s t)` and `Fix(bStar s t) ≅ T(aStar s t, bStar s t)`
unconditionally — Scott's `D ≅ S(D,E)`, `E ≅ T(D,E)`. -/
theorem fixedDomain_aStar_bStar_iso (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      IsFinitaryProjection (binOp s a b) ∧ IsFinitaryProjection (binOp t a b))
    (S T : ApproximableMap E E → ApproximableMap E E → Σ β : Type, NeighborhoodSystem β)
    (hS : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      Nonempty (Fix (binOp s a b) ≃o (S a b).2.Element))
    (hT : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      Nonempty (Fix (binOp t a b) ≃o (T a b).2.Element)) :
    Nonempty (Fix (aStar s t) ≃o (S (aStar s t) (bStar s t)).2.Element) ∧
      Nonempty (Fix (bStar s t) ≃o (T (aStar s t) (bStar s t)).2.Element) := by
  obtain ⟨hFinA, hFinB⟩ := isFinitaryProjection_aStar_bStar s t hst
  have h1 := hS (aStar s t) (bStar s t) hFinA hFinB
  have h2 := hT (aStar s t) (bStar s t) hFinA hFinB
  rw [binOp_aStar_bStar_left] at h1
  rw [binOp_aStar_bStar_right] at h2
  exact ⟨h1, h2⟩

end Exercise824
end DomainTheory.NeighbourhoodSystems
