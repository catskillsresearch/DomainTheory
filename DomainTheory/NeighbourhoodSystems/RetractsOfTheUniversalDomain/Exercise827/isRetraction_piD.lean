module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDApply_toElementMap_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


/-- **`Π(d)` is a retraction, for any `d`.** -/
theorem isRetraction_piD (d : ApproximableMap U U) : Retraction (piD d) := by
  constructor
  apply ApproximableMap.ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_comp,
    toApproxMap_toElementMap_piD d ((piD d).toElementMap φ),
    toApproxMap_toElementMap_piD d φ]
  apply ApproximableMap.ext_of_toElementMap
  intro t
  rw [toElementMap_piDApply d (piDApply d (toApproxMap φ)) t,
    piDApply_toElementMap_eq d (toApproxMap φ) t,
    toElementMap_piDApply d (toApproxMap φ) t]
  exact toElementMap_idem_of_isRetraction
    (isFinitaryProjection_decode_subU (d.toElementMap (subU.toElementMap t))).out.1.1 _

end DomainTheory.NeighbourhoodSystems
