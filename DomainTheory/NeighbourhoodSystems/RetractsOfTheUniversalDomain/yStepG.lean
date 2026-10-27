module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xStepG

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

noncomputable def yStepG (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : Set α × Set β :=
  (xyStep splitY B1 A1 Yn b).swap

end StepGen

namespace yStepG
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

theorem disjoint_of_ne {D₀ : NeighborhoodSystem α}
    {splitY : Set β → Set α → Set β → Set α × Set α} (hySplit : SplitSpec' D₀ splitY)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    {b b' : Bool} (hbb' : b ≠ b') :
    (yStepG splitY A1 B1 Yn b).1 ∩ (yStepG splitY A1 B1 Yn b').1 = ∅ ∧
      (yStepG splitY A1 B1 Yn b).2 ∩ (yStepG splitY A1 B1 Yn b').2 = ∅ := by
  have h := xyStep_disjoint_of_ne hySplit hBA hAmem Yn hbb'
  exact ⟨h.2, h.1⟩

theorem fst_subset {D₀ : NeighborhoodSystem α}
    {splitY : Set β → Set α → Set β → Set α × Set α} (hySplit : SplitSpec' D₀ splitY)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    (b : Bool) : (yStepG splitY A1 B1 Yn b).1 ⊆ A1 := by
  have hspec := hySplit hBA hAmem Yn
  by_cases hb : b = true
  · simp only [yStepG, xyStep, Prod.swap, hb, ite_true]
    exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [yStepG, xyStep, Prod.swap, hb]
    exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

theorem fst_union {D₀ : NeighborhoodSystem α}
    {splitY : Set β → Set α → Set β → Set α × Set α} (hySplit : SplitSpec' D₀ splitY)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β) :
    (yStepG splitY A1 B1 Yn true).1 ∪ (yStepG splitY A1 B1 Yn false).1 = A1 := by
  have hspec := hySplit hBA hAmem Yn
  simp only [yStepG, xyStep, Prod.swap]
  exact hspec.2.2.2.2.1

theorem snd_subset (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : (yStepG splitY A1 B1 Yn b).2 ⊆ B1 := by
  by_cases hb : b = true
  · simp only [yStepG, xyStep, Prod.swap, hb, ite_true]; exact Set.inter_subset_left
  · simp only [yStepG, xyStep, Prod.swap, hb]; exact Set.sdiff_subset

theorem snd_union (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) :
    (yStepG splitY A1 B1 Yn true).2 ∪ (yStepG splitY A1 B1 Yn false).2 = B1 := by
  simp only [yStepG, xyStep, Prod.swap]
  exact Set.inter_union_sdiff B1 Yn

end StepGen

end yStepG

end DomainTheory.NeighbourhoodSystems
