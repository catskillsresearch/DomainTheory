module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toApproxMap_toElementMap_expMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ExpMap

variable {γ δ γ' δ' γ'' δ'' : Type*}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

/-- **`expMap` preserves identities: `expMap I I = I`.** -/
theorem expMap_id : expMap (idMap V0) (idMap V1) = idMap (funSpace V0 V1) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv V0 V1).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_idMap,
    toApproxMap_toElementMap_expMap, comp_idMap, idMap_comp]

end ExpMap

end DomainTheory.NeighbourhoodSystems
