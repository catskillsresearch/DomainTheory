module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **The `X`-sub-step**, as an instance of `xyStep`: split `D₁`'s side while directly refining
`D₀`'s side. -/
noncomputable def xStep {α β : Type*} (D₁ : NeighborhoodSystem β) (hD₁nomin : D₁.NoMinimal)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : Set α × Set β :=
  xyStep (splitChoice' D₁ hD₁nomin) A B Xn b

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xStep

open NeighborhoodSystem

/-- **`xStep`'s `α`-side output is always a subset of `A`** (unconditional: `A ∩ Xn` and `A \ Xn`
are both `⊆ A`). -/
theorem fst_subset {α β : Type*} (D₁ : NeighborhoodSystem β) (hD₁nomin : D₁.NoMinimal)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : (xStep D₁ hD₁nomin A B Xn b).1 ⊆ A := by
  by_cases hb : b = true
  · simp only [xStep, xyStep, hb, ite_true]; exact Set.inter_subset_left
  · simp only [xStep, xyStep, hb]; exact Set.sdiff_subset

end xStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xStep

open NeighborhoodSystem

/-- **`xStep`'s `β`-side output is a subset of `B`**, given the `SplitSpec'` preconditions
(`I ∪ J = B`, so both `I ⊆ B` and `J ⊆ B`). -/
theorem snd_subset {α β : Type*} {D₁ : NeighborhoodSystem β} (hD₁nomin : D₁.NoMinimal)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    (b : Bool) : (xStep D₁ hD₁nomin A B Xn b).2 ⊆ B := by
  have hspec := splitChoice'_isSplitSpec D₁ hD₁nomin hAB hBmem Xn
  by_cases hb : b = true
  · simp only [xStep, xyStep, hb, ite_true]; exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [xStep, xyStep, hb]; exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

end xStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xStep

open NeighborhoodSystem

/-- **`xStep`'s two outputs, at two different sign bits, are pairwise disjoint.** -/
theorem disjoint_of_ne {α β : Type*} {D₁ : NeighborhoodSystem β} (hD₁nomin : D₁.NoMinimal)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    {b b' : Bool} (hbb' : b ≠ b') :
    (xStep D₁ hD₁nomin A B Xn b).1 ∩ (xStep D₁ hD₁nomin A B Xn b').1 = ∅ ∧
      (xStep D₁ hD₁nomin A B Xn b).2 ∩ (xStep D₁ hD₁nomin A B Xn b').2 = ∅ :=
  xyStep_disjoint_of_ne (splitChoice'_isSplitSpec D₁ hD₁nomin) hAB hBmem Xn hbb'

end xStep
end DomainTheory.NeighbourhoodSystems
