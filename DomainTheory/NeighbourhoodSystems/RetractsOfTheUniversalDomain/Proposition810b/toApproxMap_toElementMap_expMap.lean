module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ExpMap

variable {γ δ γ' δ' γ'' δ'' : Type*}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

/-- **`expMap h k`, transported through `funSpaceEquiv`, is exactly `f ↦ k∘f∘h`.** Verbatim
`toApproxMap_toElementMap_lamComb`'s proof (`Proposition810.lean`), generalized away from
self-maps. -/
theorem toApproxMap_toElementMap_expMap (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1')
    (φ : (funSpace V0 V1).Element) :
    toApproxMap ((expMap h k).toElementMap φ) = k.comp ((toApproxMap φ).comp h) := by
  apply ext_of_toElementMap
  intro z
  rw [expMap_eq, toElementMap_curry_apply, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap_pair, toElementMap_idMap, evalMap_apply, toElementMap_comp,
    toElementMap_comp]

end ExpMap

end DomainTheory.NeighbourhoodSystems
