/-ai
If the intersection of the i-th and j-th sets of the second enumeration is a neighbourhood of D₁, then that intersection equals some set of the enumeration, and the corresponding YPseq sets have the same intersection.

The covering names the intersection as some set of the enumeration. The equivalence between intersections on the two sides pushes that equation across to YPseq.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_inter_eq_iff_Y_inter_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne hYcover in
/-- **Exercise 8.12(c)(vii)(3), `exists_inter_index` (`D₁ → D₀` direction).** Symmetric to
`exists_inter_index_X`, using `hYcover` and `YPseq_inter_eq_iff_Y_inter_eq`. -/
theorem exists_inter_index_Y {i j : ℕ} (hDij : D₁.mem (Y i ∩ Y j)) :
    ∃ m, Y i ∩ Y j = Y m ∧
      YPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j =
        YPseq D₀ D₁ hD₀nomin hD₁nomin X Y m := by
  obtain ⟨m, hm⟩ := (hYcover (Y i ∩ Y j)).mp hDij
  exact ⟨m, hm, (YPseq_inter_eq_iff_Y_inter_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne i j m).mpr hm⟩

end Iso

end DomainTheory.NeighbourhoodSystems
