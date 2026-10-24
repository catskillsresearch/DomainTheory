module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.G
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkA
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkX
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkY
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.smul_assoc
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.sunion_mul
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.smul_union
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.arden

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet_subset
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


/-- **Exercise 5.15(2), leastness.** Any solution `(x, y)` of the system dominates `(x₀, y₀)`. Hence
`(x₀, y₀)` is the *least* solution, and `x₀ = (a ∪ b·a*·b)*·(c ∪ b·a*·d)` as claimed. The proof is
Gaussian elimination: solve the second equation for `y` by `arden`, substitute, apply `arden`
again. -/
theorem park_least (a b c d : Set S) {x y : Set S}
    (hx : x = a * x ∪ b * y ∪ c) (hy : y = b * x ∪ a * y ∪ d) :
    parkX a b c d ⊆ x ∧ parkY a b c d ⊆ y := by
  have hax : a * x ⊆ x := by
    calc a * x ⊆ a * x ∪ b * y ∪ c := Set.subset_union_left.trans Set.subset_union_left
      _ = x := hx.symm
  have hby : b * y ⊆ x := by
    calc b * y ⊆ a * x ∪ b * y ∪ c := Set.subset_union_right.trans Set.subset_union_left
      _ = x := hx.symm
  have hcx : c ⊆ x := by
    calc c ⊆ a * x ∪ b * y ∪ c := Set.subset_union_right
      _ = x := hx.symm
  have hay : a * y ⊆ y := by
    calc a * y ⊆ b * x ∪ a * y ∪ d := Set.subset_union_right.trans Set.subset_union_left
      _ = y := hy.symm
  have hbx : b * x ⊆ y := by
    calc b * x ⊆ b * x ∪ a * y ∪ d := Set.subset_union_left.trans Set.subset_union_left
      _ = y := hy.symm
  have hdy : d ⊆ y := by
    calc d ⊆ b * x ∪ a * y ∪ d := Set.subset_union_right
      _ = y := hy.symm
  -- The eliminated `y`: `a*·(b·x ∪ d) ⊆ y`.
  have hpre : a * y ∪ (b * x ∪ d) ⊆ y := Set.union_subset hay (Set.union_subset hbx hdy)
  have hyy : star a * (b * x ∪ d) ⊆ y := by
    rw [← arden a (b * x ∪ d)]
    exact lfpSet_subset (G a (b * x ∪ d)) hpre
  -- The decisive identity `(b·a*·b)·x ∪ b·a*·d = b·(a*·(b·x ∪ d))`.
  have key : b * star a * b * x ∪ b * star a * d = b * (star a * (b * x ∪ d)) := by
    simp only [smul_assoc, smul_union]
  -- `x` is a prefixed point of `w ↦ A·w ∪ C`, so `x₀ ⊆ x`.
  have hprefixX : parkA a b * x ∪ parkC a b c d ⊆ x := by
    have hmid : b * star a * b * x ∪ b * star a * d ⊆ x := by
      rw [key]; exact (Set.mul_subset_mul_left hyy).trans hby
    have hm1 : b * star a * b * x ⊆ x := Set.subset_union_left.trans hmid
    have hm2 : b * star a * d ⊆ x := Set.subset_union_right.trans hmid
    unfold parkA parkC
    rw [sunion_mul]
    exact Set.union_subset (Set.union_subset hax hm1) (Set.union_subset hcx hm2)
  have hPX : parkX a b c d ⊆ x := by
    have harden : parkX a b c d = lfpSet (G (parkA a b) (parkC a b c d)) :=
      (arden (parkA a b) (parkC a b c d)).symm
    rw [harden]
    exact lfpSet_subset (G (parkA a b) (parkC a b c d)) hprefixX
  have hPY : parkY a b c d ⊆ y := by
    show star a * (b * parkX a b c d ∪ d) ⊆ y
    have h1 : b * parkX a b c d ∪ d ⊆ b * x ∪ d :=
      Set.union_subset_union_left d (Set.mul_subset_mul_left hPX)
    exact (Set.mul_subset_mul_left h1).trans hyy
  exact ⟨hPX, hPY⟩

end DomainTheory.NeighbourhoodSystems.Exercise515
