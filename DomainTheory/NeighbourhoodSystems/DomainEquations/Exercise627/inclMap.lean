module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.incl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.incl_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The inclusion `i : 𝒟 →⊥ ℰ ↪ 𝒟 → ℰ`. -/
def inclMap : ApproximableMap (strictFun V₀ V₁) (funSpace V₀ V₁) :=
  ofMono (fun _ hW => incl ((strictFun V₀ V₁).principal hW))
    (fun _ _ hW hW' hW'W => incl_mono (((strictFun V₀ V₁).principal_le_iff hW hW').mpr hW'W))

end Part5

end Exercise627

end DomainTheory.NeighbourhoodSystems
