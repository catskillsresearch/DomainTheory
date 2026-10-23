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

/-- **The `Y`-sub-step**, symmetric to `xStep`: split `D₀`'s side while directly refining `D₁`'s
side. The `.swap` puts the output back into `(α-side, β-side)` order, matching `atomPair`'s own
`(A2, B2)` convention (`xyStep`'s first component is always the *direct* side, which for the
`Y`-sub-step is the `β`-side). -/
noncomputable def yStep {α β : Type*} (D₀ : NeighborhoodSystem α) (hD₀nomin : D₀.NoMinimal)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : Set α × Set β :=
  (xyStep (splitChoice' D₀ hD₀nomin) B1 A1 Yn b).swap

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace yStep

open NeighborhoodSystem

/-- **`yStep`'s two outputs, at two different sign bits, are pairwise disjoint.** -/
theorem disjoint_of_ne {α β : Type*} {D₀ : NeighborhoodSystem α} (hD₀nomin : D₀.NoMinimal)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    {b b' : Bool} (hbb' : b ≠ b') :
    (yStep D₀ hD₀nomin A1 B1 Yn b).1 ∩ (yStep D₀ hD₀nomin A1 B1 Yn b').1 = ∅ ∧
      (yStep D₀ hD₀nomin A1 B1 Yn b).2 ∩ (yStep D₀ hD₀nomin A1 B1 Yn b').2 = ∅ := by
  have h := xyStep_disjoint_of_ne (splitChoice'_isSplitSpec D₀ hD₀nomin) hBA hAmem Yn hbb'
  exact ⟨h.2, h.1⟩

end yStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace yStep

open NeighborhoodSystem

/-- **`yStep`'s `α`-side output is a subset of `A1`**, given the `SplitSpec'` preconditions. -/
theorem fst_subset {α β : Type*} {D₀ : NeighborhoodSystem α} (hD₀nomin : D₀.NoMinimal)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    (b : Bool) : (yStep D₀ hD₀nomin A1 B1 Yn b).1 ⊆ A1 := by
  have hspec := splitChoice'_isSplitSpec D₀ hD₀nomin hBA hAmem Yn
  by_cases hb : b = true
  · simp only [yStep, xyStep, Prod.swap, hb, ite_true]
    exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [yStep, xyStep, Prod.swap, hb]
    exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

end yStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace yStep

open NeighborhoodSystem

/-- **`yStep`'s `β`-side output is always a subset of `B1`** (unconditional). -/
theorem snd_subset {α β : Type*} (D₀ : NeighborhoodSystem α) (hD₀nomin : D₀.NoMinimal)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : (yStep D₀ hD₀nomin A1 B1 Yn b).2 ⊆ B1 := by
  by_cases hb : b = true
  · simp only [yStep, xyStep, Prod.swap, hb, ite_true]; exact Set.inter_subset_left
  · simp only [yStep, xyStep, Prod.swap, hb]; exact Set.sdiff_subset

end yStep
end DomainTheory.NeighbourhoodSystems
