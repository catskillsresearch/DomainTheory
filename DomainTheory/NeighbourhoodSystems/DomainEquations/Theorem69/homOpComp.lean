module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.isStrict_comp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

section HomOp

variable (T : Endofunctor DomainObj) (D E : DomainObj)
  (j : ApproximableMap D.sys (T.obj D).sys)
  (k : ApproximableMap (T.obj E).sys E.sys)
  (hj : IsStrict j) (hk : IsStrict k)

/-- The strict composite `g ↦ k ∘ g ∘ j : (T(D) →⊥ T(E)) → (D →⊥ E)`. -/
def homOpComp (g : StrictMap (T.obj D).sys (T.obj E).sys) : StrictMap D.sys E.sys :=
  ⟨k.comp (g.1.comp j), isStrict_comp hk (isStrict_comp g.2 hj)⟩

end HomOp

end DomainTheory.NeighbourhoodSystems
