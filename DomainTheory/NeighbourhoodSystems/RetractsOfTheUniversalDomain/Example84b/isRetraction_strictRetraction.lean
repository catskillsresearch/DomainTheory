module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.toApproxMap_injective

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}







section Strict








theorem isRetraction_strictRetraction : IsRetraction (strictRetraction (D := D) (E := E)) := by
  apply ext_of_toElementMap
  intro φ
  rw [toElementMap_comp]
  apply toApproxMap_injective
  apply ext_of_toElementMap
  intro y
  by_cases hy : y = D.bot
  · rw [hy, strictRetraction_apply_bot, strictRetraction_apply_bot]
  · rw [strictRetraction_apply_of_ne_bot hy, strictRetraction_apply_of_ne_bot hy]

end Strict
end DomainTheory.NeighbourhoodSystems
