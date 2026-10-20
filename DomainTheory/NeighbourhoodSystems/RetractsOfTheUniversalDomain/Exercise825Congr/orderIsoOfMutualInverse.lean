module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Two approximable maps that are *exact* (not merely `≤`) mutual inverses give an
order-isomorphism of element types.** The generic upgrade behind `elementIsoOfProjectionPair`
(`Proposition810b.lean`) when the projection-pair equation holds in *both* directions: then the
fixed-point subtype on the codomain side is *everything*, collapsing to a genuine bijection. -/
def orderIsoOfMutualInverse {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) (hij : i.comp j = idMap E) : D.Element ≃o E.Element where
  toFun := i.toElementMap
  invFun := j.toElementMap
  left_inv x := by rw [← toElementMap_comp, hji, toElementMap_idMap]
  right_inv y := by rw [← toElementMap_comp, hij, toElementMap_idMap]
  map_rel_iff' := by
    intro x x'
    show i.toElementMap x ≤ i.toElementMap x' ↔ x ≤ x'
    constructor
    · intro h
      have hm := j.toElementMap_mono h
      rwa [← toElementMap_comp, ← toElementMap_comp, hji, toElementMap_idMap,
        toElementMap_idMap] at hm
    · intro h
      exact i.toElementMap_mono h

end DomainTheory.NeighbourhoodSystems
