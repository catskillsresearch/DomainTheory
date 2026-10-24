module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fade₂
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fade
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fin2_zero_subset_zero_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fin2_zero_ne_zero_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_master_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.exists_mem_ne_master_of_ne_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap_check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.toElementMap_ofMap₂_pair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap₂_fade
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO_ne_bot_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.toElementMap_a_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_toElementMap_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO_check_toElementMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_le_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO_mono
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
