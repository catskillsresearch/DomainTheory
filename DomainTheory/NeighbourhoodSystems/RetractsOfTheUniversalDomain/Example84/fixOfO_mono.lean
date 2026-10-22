module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_le_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

variable (u : D.Element) (hu : u ≠ D.bot)

theorem fixOfO_mono {t t' : O.Element} (h : t ≤ t') : fixOfO u t ≤ fixOfO u t' := by
  intro Z hZ
  rw [mem_fixOfO] at hZ ⊢
  obtain ⟨hZD, hZeq | ⟨ht0, huZ⟩⟩ := hZ
  · exact ⟨hZD, Or.inl hZeq⟩
  · exact ⟨hZD, Or.inr ⟨O_le_iff.mp h ht0, huZ⟩⟩

end DomainTheory.NeighbourhoodSystems
