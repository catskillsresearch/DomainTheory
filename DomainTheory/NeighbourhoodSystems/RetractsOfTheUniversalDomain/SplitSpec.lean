module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.subApprox

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
open NeighborhoodSystem
variable {α : Type*}

/-- **The abstract specification a splitting operation must satisfy** — exactly `exists_split`'s
conclusion, as a `Prop` about a *total* function `split`. Both the classical `splitChoice` (via
`Classical.choice`) and the effective, computable `splitEff` (Theorem 8.8(b)) satisfy this. -/
def SplitSpec (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ) : Prop :=
  ∀ {A : Set α} {B : Set ℚ}, (A = ∅ ↔ B = ∅) → (B = ∅ ∨ U.mem B) → ∀ Xn : Set α,
    ((split A B Xn).1 = ∅ ∨ U.mem (split A B Xn).1) ∧
      ((split A B Xn).2 = ∅ ∨ U.mem (split A B Xn).2) ∧
      (A ∩ Xn = ∅ ↔ (split A B Xn).1 = ∅) ∧
      (A \ Xn = ∅ ↔ (split A B Xn).2 = ∅) ∧
      (split A B Xn).1 ∪ (split A B Xn).2 = B ∧
      (split A B Xn).1 ∩ (split A B Xn).2 = ∅

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
      obtain ⟨Y, Z, hY, hZ, hYZinter, hYZunion, -, -⟩ := U.no_minimal hBU'
      have hYne : Y ≠ ∅ := hY.2.1.ne_empty
      have hZne : Z ≠ ∅ := hZ.2.1.ne_empty
      exact ⟨Y, Z, Or.inr hY, Or.inr hZ, iff_of_false h1 hYne, iff_of_false h2 hZne,
        hYZunion, hYZinter⟩

def genAtom {β : Type*} (Z : ℕ → Set β) (M : Set β) (δ : ℕ → Bool) : ℕ → Set β
  | 0 => M
  | (n + 1) => genAtom Z M δ n ∩ (if δ n then Z n else M \ Z n)

end

end DomainTheory.NeighbourhoodSystems
