module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitSpec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Yseq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

/-- Scott's Definition 8.7: the universal neighbourhood system on `[0, 1)` consists of
nonempty finite unions of rational subintervals; it has no minimal neighbourhoods, the
canonical split satisfies `SplitSpec`, $Y$-sequences are unions of atoms in `U`, and the
initial atom is the master neighbourhood. -/
theorem definition_87 {α : Type*} :
    (U.master = UMaster) ∧
      (∀ X : Set ℚ, U.mem X ↔
        ∃ L : List (ℚ × ℚ), (∀ p ∈ L, (0 : ℚ) ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1) ∧
          X = presentedIntervals L ∧ X.Nonempty) ∧
        U.NoMinimal ∧
        SplitSpec (α := α) splitChoice ∧
        (∀ (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ) (X : ℕ → Set α) (Δ : Set α) (δ : ℕ → Bool),
          atomU split X Δ δ 0 = U.master) ∧
        (∀ (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ) (X : ℕ → Set α) (Δ : Set α)
            (_hΔ : Δ.Nonempty) (_hsplit : SplitSpec split) (n : ℕ),
          Yseq split X Δ n = ∅ ∨ U.mem (Yseq split X Δ n)) :=
  ⟨rfl, fun X => U.mem_iff_scott (X := X), U.noMinimal, splitChoice_isSplitSpec,
    fun split X Δ δ => atomU_zero split X Δ δ,
    fun split X Δ _hΔ _hsplit n => Yseq_empty_or_mem split X Δ _hΔ _hsplit n⟩

end DomainTheory.NeighbourhoodSystems
