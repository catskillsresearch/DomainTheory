module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.lambR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.envR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem envR_isRetract : Retract envR := by
  constructor
  change envR = graph (fun t => funOf envR (funOf envR t))
  apply graph_ext
  intro t
  rw [envR_app, envR_app]
  apply graph_ext
  intro n
  have hβ : funOf (graph (fun m => funOf lambR (funOf t m))) n =
      funOf lambR (funOf t n) :=
    beta (theorem_1_3 (funOf_isScottContinuous lambR)
      (funOf_isScottContinuous t)) n
  rw [hβ, retract_app lambR_isRetract]

end DomainTheory.DataTypesAsLattices
