module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

/-- **Generalized `yStep`**: split `D₀`'s side (via the abstract `splitY`) while directly refining
`D₁`'s side. Literally `(xyStep splitY _ _ _ _).swap`; `yStep D₀ hD₀nomin = yStepG (splitChoice' D₀
hD₀nomin)`. -/
noncomputable def yStepG (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : Set α × Set β :=
  (xyStep splitY B1 A1 Yn b).swap

end StepGen

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
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

end StepGen

end yStepG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace yStepG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

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

end StepGen

end yStepG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace yStepG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

/-- **`yStepG`'s two split-side outputs reunion to exactly the split's own input `A1`**: from
`SplitSpec'`'s unconditional `(split A B Xn).1 ∪ (split A B Xn).2 = B` field (here with `B := A1`,
`A := B1`, matching `yStepG`'s `.swap`-ed argument order). Needed for **8.12(d)(4)(c)(i)**'s
one-step 4-way reunion (the `b2`-level half). -/
theorem fst_union {D₀ : NeighborhoodSystem α}
    {splitY : Set β → Set α → Set β → Set α × Set α} (hySplit : SplitSpec' D₀ splitY)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β) :
    (yStepG splitY A1 B1 Yn true).1 ∪ (yStepG splitY A1 B1 Yn false).1 = A1 := by
  have hspec := hySplit hBA hAmem Yn
  simp only [yStepG, xyStep, Prod.swap]
  exact hspec.2.2.2.2.1

end StepGen

end yStepG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace yStepG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

theorem snd_subset (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : (yStepG splitY A1 B1 Yn b).2 ⊆ B1 := by
  by_cases hb : b = true
  · simp only [yStepG, xyStep, Prod.swap, hb, ite_true]; exact Set.inter_subset_left
  · simp only [yStepG, xyStep, Prod.swap, hb]; exact Set.sdiff_subset

end StepGen

end yStepG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace yStepG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

/-- **`yStepG`'s two direct-refine outputs reunion to exactly its own input `B1`**: the trivial
two-set identity `(B1 ∩ Yn) ∪ (B1 \ Yn) = B1`, restated through `yStepG`'s `.2` (the `.swap`-ed
direct-refine side, on `D₁`'s side). Needed for **8.12(d)(4)(d)(i)**'s one-step 4-way reunion (the
`D₁`-side mirror of `xStepG.fst_union`'s `b1`-level half); no `SplitSpec'` hypotheses needed, exactly
like `xStepG.fst_union`. -/
theorem snd_union (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) :
    (yStepG splitY A1 B1 Yn true).2 ∪ (yStepG splitY A1 B1 Yn false).2 = B1 := by
  simp only [yStepG, xyStep, Prod.swap]
  exact Set.inter_union_sdiff B1 Yn

end StepGen

end yStepG
end DomainTheory.NeighbourhoodSystems
