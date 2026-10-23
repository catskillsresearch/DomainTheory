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

/-- **Generalized `xStep`**: split `D₁`'s side (via the abstract `splitX`) while directly refining
`D₀`'s side. Literally `xyStep splitX`; `xStep D₁ hD₁nomin = xStepG (splitChoice' D₁ hD₁nomin)`. -/
noncomputable def xStepG (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : Set α × Set β :=
  xyStep splitX A B Xn b

end StepGen

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xStepG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

theorem disjoint_of_ne {D₁ : NeighborhoodSystem β}
    {splitX : Set α → Set β → Set α → Set β × Set β} (hxSplit : SplitSpec' D₁ splitX)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    {b b' : Bool} (hbb' : b ≠ b') :
    (xStepG splitX A B Xn b).1 ∩ (xStepG splitX A B Xn b').1 = ∅ ∧
      (xStepG splitX A B Xn b).2 ∩ (xStepG splitX A B Xn b').2 = ∅ :=
  xyStep_disjoint_of_ne hxSplit hAB hBmem Xn hbb'

end StepGen

end xStepG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xStepG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

theorem fst_subset (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : (xStepG splitX A B Xn b).1 ⊆ A := by
  by_cases hb : b = true
  · simp only [xStepG, xyStep, hb, ite_true]; exact Set.inter_subset_left
  · simp only [xStepG, xyStep, hb]; exact Set.sdiff_subset

end StepGen

end xStepG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xStepG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

/-- **`xStepG`'s two direct-refine outputs reunion to exactly the parent**: the trivial two-set
identity `(A ∩ Xn) ∪ (A \ Xn) = A`, restated through `xStepG`'s `.1`. Needed for
**8.12(d)(4)(c)(i)**'s one-step 4-way reunion (the `b1`-level half of the argument); no `SplitSpec'`
hypotheses needed at all, unlike every other fact about `xStepG`/`yStepG` in this section. -/
theorem fst_union (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) :
    (xStepG splitX A B Xn true).1 ∪ (xStepG splitX A B Xn false).1 = A := by
  simp only [xStepG, xyStep]
  exact Set.inter_union_sdiff A Xn

end StepGen

end xStepG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xStepG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

theorem snd_subset {D₁ : NeighborhoodSystem β}
    {splitX : Set α → Set β → Set α → Set β × Set β} (hxSplit : SplitSpec' D₁ splitX)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    (b : Bool) : (xStepG splitX A B Xn b).2 ⊆ B := by
  have hspec := hxSplit hAB hBmem Xn
  by_cases hb : b = true
  · simp only [xStepG, xyStep, hb, ite_true]; exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [xStepG, xyStep, hb]; exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

end StepGen

end xStepG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xStepG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

/-- **`xStepG`'s two split-side outputs reunion to exactly its own input `B`**: from `SplitSpec'`'s
unconditional `(split A B Xn).1 ∪ (split A B Xn).2 = B` field, applied directly (no `.swap`, unlike
`yStepG.fst_union`'s use of the same field). Needed for **8.12(d)(4)(d)(i)**'s one-step 4-way
reunion (the `D₁`-side mirror of `yStepG.fst_union`'s `b2`-level half). -/
theorem snd_union {D₁ : NeighborhoodSystem β}
    {splitX : Set α → Set β → Set α → Set β × Set β} (hxSplit : SplitSpec' D₁ splitX)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α) :
    (xStepG splitX A B Xn true).2 ∪ (xStepG splitX A B Xn false).2 = B := by
  have hspec := hxSplit hAB hBmem Xn
  simp only [xStepG, xyStep]
  exact hspec.2.2.2.2.1

end StepGen

end xStepG
end DomainTheory.NeighbourhoodSystems
