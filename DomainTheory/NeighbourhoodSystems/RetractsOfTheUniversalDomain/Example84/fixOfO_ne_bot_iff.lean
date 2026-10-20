module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.exists_mem_ne_master_of_ne_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_fixOfO

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

variable (u : D.Element) (hu : u ≠ D.bot)

theorem fixOfO_ne_bot_iff (hu : u ≠ D.bot) {t : O.Element} :
    fixOfO u t ≠ D.bot ↔ t.mem ({0} : Set (Fin 2)) := by
  constructor
  · intro hne
    by_contra ht0
    apply hne
    apply Element.ext
    intro Z
    rw [mem_fixOfO, mem_bot]
    constructor
    · rintro ⟨-, rfl | ⟨ht0', -⟩⟩
      · rfl
      · exact absurd ht0' ht0
    · rintro rfl
      exact ⟨D.master_mem, Or.inl rfl⟩
  · intro ht0 hbot
    obtain ⟨Z, huZ, hZne⟩ := exists_mem_ne_master_of_ne_bot hu
    have : (fixOfO u t).mem Z := ⟨u.sub huZ, Or.inr ⟨ht0, huZ⟩⟩
    rw [hbot, mem_bot] at this
    exact hZne this

end DomainTheory.NeighbourhoodSystems
