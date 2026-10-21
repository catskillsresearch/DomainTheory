/-ai
The exponential preserves composition, contravariantly in the first argument: the exponential of a composite h after h' and a composite k' after k equals the exponential of h' and k' composed after the exponential of h and k.

Compare elements of the function space, and apply the function-space equivalence, which is injective. The elementwise form of the exponential turns both sides into the corresponding composites of maps, and associativity identifies them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toApproxMap_toElementMap_expMap

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

/-- **`expMap` preserves composition, contravariantly in `h`:
`expMap (h∘h') (k'∘k) = expMap h' k' ∘ expMap h k`.** -/
theorem expMap_comp (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1')
    (h' : ApproximableMap V0'' V0') (k' : ApproximableMap V1' V1'') :
    expMap (h.comp h') (k'.comp k) = (expMap h' k').comp (expMap h k) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv V0'' V1'').injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toElementMap_expMap, toElementMap_comp,
    toApproxMap_toElementMap_expMap, toApproxMap_toElementMap_expMap]
  simp only [comp_assoc]

end ExpMap

end DomainTheory.NeighbourhoodSystems
