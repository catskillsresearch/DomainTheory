module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.a_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.a_of_ne_bot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂


variable {α : Type*} {D : NeighborhoodSystem α}


variable (u : D.Element) (hu : u ≠ D.bot)


/-- **Example 8.4(a) (Scott 1981, PRG-19).** `a` is a retraction. -/
theorem isRetraction_a (hu : u ≠ D.bot) : Retraction (a u) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  by_cases hx : x = D.bot
  · subst hx; rw [a_bot, a_bot]
  · rw [a_of_ne_bot u hx, a_of_ne_bot u hu]

end DomainTheory.NeighbourhoodSystems
