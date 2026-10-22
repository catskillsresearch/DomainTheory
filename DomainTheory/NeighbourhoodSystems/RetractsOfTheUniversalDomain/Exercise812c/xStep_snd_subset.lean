module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.splitChoice'_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xyStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`xStep`'s `β`-side output is a subset of `B`**, given the `SplitSpec'` preconditions
(`I ∪ J = B`, so both `I ⊆ B` and `J ⊆ B`). -/
theorem xStep_snd_subset {α β : Type*} {D₁ : NeighborhoodSystem β} (hD₁nomin : D₁.NoMinimal)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    (b : Bool) : (xStep D₁ hD₁nomin A B Xn b).2 ⊆ B := by
  have hspec := splitChoice'_isSplitSpec D₁ hD₁nomin hAB hBmem Xn
  by_cases hb : b = true
  · simp only [xStep, xyStep, hb, ite_true]; exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [xStep, xyStep, hb]; exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

end DomainTheory.NeighbourhoodSystems
