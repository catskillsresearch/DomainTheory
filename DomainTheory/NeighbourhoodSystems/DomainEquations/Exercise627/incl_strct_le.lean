/-ai
Inclusion of the strictification of a function-space element lies below that element.

The composite equals the filter of the relational strictification of the approximable map of the element, because the strict map of the strictification is the strictification of that approximable map. Rewriting the original element as the filter of its approximable map, the inequality is the image, under the inverse function-space equivalence, of the inequality of a strictified map below the original map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictifyMap_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toFilter_toApproxMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toStrictMap_toStrictFilter

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










theorem incl_strct_le (ψ : (funSpace V₀ V₁).Element) : incl (strct ψ) ≤ ψ := by
  have key : incl (strct ψ) = toFilter (strictifyMap (toApproxMap ψ)) := by
    show toFilter (toStrictMap (strct ψ)).1 = toFilter (strictifyMap (toApproxMap ψ))
    rw [show toStrictMap (strct ψ) = strictify (toApproxMap ψ) from toStrictMap_toStrictFilter _]
    rfl
  rw [key]
  conv_rhs => rw [← toFilter_toApproxMap ψ]
  exact (funSpaceEquiv V₀ V₁).symm.monotone (strictifyMap_le (toApproxMap ψ))

end Part5
end Exercise627
end DomainTheory.NeighbourhoodSystems
