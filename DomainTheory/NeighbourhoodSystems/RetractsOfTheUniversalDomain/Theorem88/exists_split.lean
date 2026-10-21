/-ai
Given a set A matched with a set B of rationals, so that A is empty exactly when B is empty and B is empty or a neighbourhood of U, and given a further set, there are sets I and J of rationals, each empty or a neighbourhood of U, with I empty exactly when A meets the further set is empty, J empty exactly when the difference is empty, with union B, and with empty intersection.

If the intersection is empty, I is empty and J is B. The difference then equals A, because a point of A cannot meet the further set, so emptiness of the difference matches emptiness of A and hence of B. If the intersection is nonempty and the difference is empty, I is B and J is empty. The intersection then equals A, because a point of A cannot lie outside the further set, so its emptiness matches emptiness of A and hence of B. If both are nonempty, A is nonempty, so B is nonempty and therefore a neighbourhood of U. The splitting of a neighbourhood of U with no minimal piece supplies two neighbourhoods that are disjoint, union to B, and nonempty, and both sides of each emptiness equivalence are false.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
import all Mathlib.Data.Fintype.Pi

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-- **The key local splitting step behind Theorem 8.8(a)'s back-and-forth construction.** Given a
`D`-side atom `A` matched with a `U`-side atom `B` (`A = ∅ ↔ B = ∅`, and `B` is either empty or a
genuine `U`-neighbourhood), and a new target set `Xₙ` (morally the next `D`-neighbourhood `Xₙ`),
produce matching refinements `I` (for `A ∩ Xₙ`) and `J` (for `A \ Xₙ`). -/
theorem exists_split {A : Set α} {B : Set ℚ} (hAB : A = ∅ ↔ B = ∅)
    (hBU : B = ∅ ∨ U.mem B) (Xn : Set α) :
    ∃ I J : Set ℚ, (I = ∅ ∨ U.mem I) ∧ (J = ∅ ∨ U.mem J) ∧
      (A ∩ Xn = ∅ ↔ I = ∅) ∧ (A \ Xn = ∅ ↔ J = ∅) ∧ I ∪ J = B ∧ I ∩ J = ∅ := by
  by_cases h1 : A ∩ Xn = ∅
  · refine ⟨∅, B, Or.inl rfl, hBU, by simp [h1], ?_, by simp, by simp⟩
    have hAeq : A \ Xn = A := by
      ext x
      simp only [Set.mem_sdiff]
      refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun hxn => ?_⟩⟩
      exact Set.eq_empty_iff_forall_notMem.mp h1 x ⟨hx, hxn⟩
    rw [hAeq, hAB]
  · by_cases h2 : A \ Xn = ∅
    · refine ⟨B, ∅, hBU, Or.inl rfl, ?_, iff_of_true h2 rfl, by simp, by simp⟩
      have hAeq : A ∩ Xn = A := by
        ext x
        simp only [Set.mem_inter_iff]
        refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
        by_contra hxn
        exact Set.eq_empty_iff_forall_notMem.mp h2 x ⟨hx, hxn⟩
      rw [hAeq, hAB]
    · have hAne : A ≠ ∅ := by
        intro hA
        apply h1
        rw [hA]
        exact Set.empty_inter Xn
      have hBne : B ≠ ∅ := fun hB => hAne (hAB.mpr hB)
      have hBU' : U.mem B := hBU.resolve_left hBne
      obtain ⟨Y, Z, hY, hZ, hYZinter, hYZunion, -, -⟩ := U_no_minimal hBU'
      have hYne : Y ≠ ∅ := hY.2.1.ne_empty
      have hZne : Z ≠ ∅ := hZ.2.1.ne_empty
      exact ⟨Y, Z, Or.inr hY, Or.inr hZ, iff_of_false h1 hYne, iff_of_false h2 hZne,
        hYZunion, hYZinter⟩

end DomainTheory.NeighbourhoodSystems
