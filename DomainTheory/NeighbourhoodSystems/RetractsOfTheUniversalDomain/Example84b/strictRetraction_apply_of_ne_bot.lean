module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_fst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_snd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.toApproxMap_strictRetraction_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

theorem strictRetraction_apply_of_ne_bot {y : D.Element} (hy : y ≠ D.bot)
    (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap y
      = (toApproxMap φ).toElementMap y := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem]
  constructor
  · rintro ⟨-, rfl | ⟨-, hZ⟩⟩
    · exact ((toApproxMap φ).toElementMap y).master_mem
    · exact hZ
  · intro hZ
    exact ⟨((toApproxMap φ).toElementMap y).sub hZ, Or.inr ⟨hy, hZ⟩⟩

end Strict

end DomainTheory.NeighbourhoodSystems
