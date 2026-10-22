module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strct
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strct_mono

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The strictification retraction `j : 𝒟 → ℰ → 𝒟 →⊥ ℰ`. -/
def strctMap : ApproximableMap (funSpace V₀ V₁) (strictFun V₀ V₁) :=
  ofMono (fun _ hM => strct ((funSpace V₀ V₁).principal hM))
    (fun _ _ hM hM' hM'M => strct_mono (((funSpace V₀ V₁).principal_le_iff hM hM').mpr hM'M))

end Part5

end Exercise627

end DomainTheory.NeighbourhoodSystems
