module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap
































/-- **`Π(d) ≤ I`, for any `d`.** Chains: `subU(t) ⊑ t` (`subU`'s own projection property) with
`f`'s monotonicity to get `f(subU(t)) ⊑ f(t)`, then the "type at `t`"'s own `≤ I` (from
`isFinitaryProjection_decode_subU`) to get `(type at t)(f(subU(t))) ⊑ f(subU(t))`. -/
theorem le_idMap_piD (d : ApproximableMap U U) : piD d ≤ idMap (funSpace U U) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_idMap, ← (funSpaceEquiv U U).le_iff_le, funSpaceEquiv_apply,
    funSpaceEquiv_apply, toApproxMap_toElementMap_piD, le_iff_toElementMap_le]
  intro t
  rw [toElementMap_piDApply]
  have hP := (isFinitaryProjection_decode_subU (d.toElementMap (subU.toElementMap t))).1.2
  calc (toApproxMap (jArrow.toElementMap (subU.toElementMap
        (d.toElementMap (subU.toElementMap t))))).toElementMap
        ((toApproxMap φ).toElementMap (subU.toElementMap t))
      ≤ (toApproxMap φ).toElementMap (subU.toElementMap t) :=
        toElementMap_le_self_of_le_idMap hP _
    _ ≤ (toApproxMap φ).toElementMap t :=
        (toApproxMap φ).toElementMap_mono
          (toElementMap_le_self_of_le_idMap isProjection_subU.2 t)

end DomainTheory.NeighbourhoodSystems
