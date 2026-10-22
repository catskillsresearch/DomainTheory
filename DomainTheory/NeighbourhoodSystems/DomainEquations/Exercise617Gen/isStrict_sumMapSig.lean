module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.SigTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjU_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- The sum map is strict: it sends `⊥ = master` only to `master`. -/
theorem isStrict_sumMapSig (f : ApproximableMap V₀ V₁) :
    IsStrict (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f) := by
  rintro W' ⟨-, -, hd⟩
  rcases hd with rfl | ⟨hWU, -⟩ | ⟨a, X, Y', hWX, -, -⟩
  · rfl
  · exact absurd (hWU ▸ (show (none : SigTok A β₀) ∈ (sumSig A V₀ h₀).master from
      none_mem_masterSig)) none_not_mem_jU
  · exact absurd (hWX ▸ (show (none : SigTok A β₀) ∈ (sumSig A V₀ h₀).master from
      none_mem_masterSig)) none_not_mem_jc

end SumMapSig

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
