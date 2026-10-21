/-ai
Check sends the fixed-point element associated with an element of the two-point system back to that element.

Extensionality, after rewriting by the membership criterion of check and by the criterion that the fixed-point element differs from bottom, unpacks a two-point membership and a disjunction. An equality with the master rewrites to master membership of the element. The other alternative splits the two-point membership into the singleton, which is the membership already obtained, or the master, which belongs to the element. Conversely, a neighbourhood of the element is a neighbourhood of the two-point system, hence the singleton, which is the right alternative, or the master, which is the left alternative.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_master_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap_check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO_ne_bot_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

variable (u : D.Element) (hu : u ≠ D.bot)

theorem check_toElementMap_fixOfO (hu : u ≠ D.bot) (t : O.Element) :
    check.toElementMap (fixOfO u t) = t := by
  apply Element.ext
  intro Y
  rw [mem_toElementMap_check, fixOfO_ne_bot_iff u hu]
  constructor
  · rintro ⟨hYO, hYeq | ht0⟩
    · rw [hYeq, ← O_master_eq]; exact t.master_mem
    · rcases hYO with rfl | rfl
      · exact ht0
      · rw [← O_master_eq]; exact t.master_mem
  · intro htY
    have hYO : O.mem Y := t.sub htY
    refine ⟨hYO, ?_⟩
    rcases O_mem_iff.mp hYO with rfl | rfl
    · exact Or.inr htY
    · exact Or.inl rfl

end DomainTheory.NeighbourhoodSystems
