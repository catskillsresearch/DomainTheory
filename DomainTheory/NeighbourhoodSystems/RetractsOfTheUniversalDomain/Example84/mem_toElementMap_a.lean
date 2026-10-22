module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fin2_zero_ne_zero_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap_check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fade₂
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fade
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.toElementMap_ofMap₂_pair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap₂_fade
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.a

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

variable (u : D.Element) (hu : u ≠ D.bot)

theorem mem_toElementMap_a {x : D.Element} {Z : Set α} :
    ((a u).toElementMap x).mem Z ↔ D.mem Z ∧ (Z = D.master ∨ (x ≠ D.bot ∧ u.mem Z)) := by
  show ((fade.comp (paired check (constMap D u))).toElementMap x).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_constMap]
  show (fade.toElementMap (pair (check.toElementMap x) u)).mem Z ↔ _
  rw [show fade = ofMap₂ fade₂ from rfl, toElementMap_ofMap₂_pair, mem_toElementMap₂_fade,
    mem_toElementMap_check]
  constructor
  · rintro ⟨hZD, hZeq | ⟨⟨-, hcase⟩, huZ⟩⟩
    · exact ⟨hZD, Or.inl hZeq⟩
    · rcases hcase with hYeq | hxne
      · exact absurd hYeq fin2_zero_ne_zero_one
      · exact ⟨hZD, Or.inr ⟨hxne, huZ⟩⟩
  · rintro ⟨hZD, hZeq | ⟨hxne, huZ⟩⟩
    · exact ⟨hZD, Or.inl hZeq⟩
    · exact ⟨hZD, Or.inr ⟨⟨O_mem_zero, Or.inr hxne⟩, huZ⟩⟩

end DomainTheory.NeighbourhoodSystems
