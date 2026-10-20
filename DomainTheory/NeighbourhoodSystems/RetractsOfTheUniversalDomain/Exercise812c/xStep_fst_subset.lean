module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xyStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`xStep`'s `α`-side output is always a subset of `A`** (unconditional: `A ∩ Xn` and `A \ Xn`
are both `⊆ A`). -/
theorem xStep_fst_subset {α β : Type*} (D₁ : NeighborhoodSystem β) (hD₁nomin : D₁.NoMinimal)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : (xStep D₁ hD₁nomin A B Xn b).1 ⊆ A := by
  by_cases hb : b = true
  · simp only [xStep, xyStep, hb, ite_true]; exact Set.inter_subset_left
  · simp only [xStep, xyStep, hb]; exact Set.sdiff_subset

end DomainTheory.NeighbourhoodSystems
