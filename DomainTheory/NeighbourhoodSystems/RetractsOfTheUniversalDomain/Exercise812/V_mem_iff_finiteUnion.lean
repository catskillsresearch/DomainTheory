module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.affine_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.affine_eq_levelSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_eq_biUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_iUnion_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **`V.mem` literally matches Scott's "non-empty finite unions of `2^k ℕ + ℓ`, `ℓ < 2^k`"** —
reconciles the bookkeeping-free `levelSet` encoding with Exercise 8.12's literal description,
mirroring `Definition87.lean`'s `U_mem_iff_scott`. -/
theorem V_mem_iff_finiteUnion {X : Set ℕ} :
    V.mem X ↔
      ∃ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.2 < 2 ^ p.1) ∧ X = ⋃ p ∈ F, affine p.1 p.2 ∧ X.Nonempty := by
  constructor
  · rintro ⟨k, m, rfl, hne⟩
    refine ⟨(Finset.range (2 ^ k)).filter (fun ℓ => m.testBit ℓ) |>.image (fun ℓ => (k, ℓ)), ?_, ?_, hne⟩
    · rintro ⟨k', ℓ⟩ hp
      obtain ⟨ℓ', hℓ', heq⟩ := Finset.mem_image.mp hp
      obtain ⟨hlt, -⟩ := Finset.mem_filter.mp hℓ'
      simp only [Finset.mem_range] at hlt
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
      exact hlt
    · rw [levelSet_eq_biUnion]
      ext n
      simp only [Set.mem_iUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
        exists_prop, exists_exists_and_eq_and]
  · rintro ⟨F, hbound, rfl, hne⟩
    have hf : ∀ p : F, affine p.1.1 p.1.2 = ∅ ∨ V.mem (affine p.1.1 p.1.2) :=
      fun ⟨p, hp⟩ => Or.inr ⟨p.1, 2 ^ p.2, affine_eq_levelSet p.1 p.2,
        affine_eq_levelSet p.1 p.2 ▸ affine_nonempty (hbound p hp)⟩
    have hrw : (⋃ p ∈ F, affine p.1 p.2) = ⋃ p : F, affine p.1.1 p.1.2 := by
      ext n; simp only [Set.mem_iUnion, exists_prop, Subtype.exists]
    rw [hrw] at hne ⊢
    exact V_iUnion_mem hf hne

end DomainTheory.NeighbourhoodSystems
