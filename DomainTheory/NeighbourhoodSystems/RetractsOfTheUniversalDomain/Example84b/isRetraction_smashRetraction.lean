module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smashRetraction_of_ne_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smashRetraction_of_eq_bot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






theorem isRetraction_smashRetraction : IsRetraction (smashRetraction (D := D) (E := E)) := by
  apply ext_of_toElementMap
  intro z
  rw [toElementMap_comp]
  by_cases hx : z.fst = D.bot
  · rw [smashRetraction_of_eq_bot (Or.inl hx),
      smashRetraction_of_eq_bot (Or.inl prod_bot_fst)]
  · by_cases hy : z.snd = E.bot
    · rw [smashRetraction_of_eq_bot (Or.inr hy),
        smashRetraction_of_eq_bot (Or.inr prod_bot_snd)]
    · rw [smashRetraction_of_ne_bot hx hy, smashRetraction_of_ne_bot hx hy]

end Smash
end DomainTheory.NeighbourhoodSystems
