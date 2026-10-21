/-ai
The approximable map of an open set relates a neighbourhood X of the domain to a neighbourhood Y of O when emptiness of Y implies that the principal filter of X lies in the open set. The master neighbourhoods are related because the master neighbourhood of O is the universe, which is not empty. If the first output neighbourhood is the universe, the intersection law reduces to the second output; if it is empty, the emptiness condition is inherited from the first. If a sharper output is empty, the original output is empty as well, and the open set is an upper set, so the principal filter of a sharper input still lies in the open set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.univ_ne_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_inter_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — the approximable map of an open set.** For open `U ⊆ |𝒟|`, the relation
`X f Y ↔ X ∈ 𝒟 ∧ Y ∈ 𝒪 ∧ (Y = ∅ → ↑X ∈ U)`. The single nontrivial obligation is monotonicity:
sharpening the input `X' ⊆ X` means `↑X ⊑ ↑X'`, and `U` open (an upper set) carries `↑X ∈ U` up to
`↑X' ∈ U`. Choice-free. -/
def openToMap (U : Set V.Element) (hU : IsOpen U) : ApproximableMap V O where
  rel X Y := V.mem X ∧ O.mem Y ∧ (Y = ∅ → ∃ hX : V.mem X, V.principal hX ∈ U)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V.master_mem, O.master_mem, fun heq => (univ_ne_empty (O_master ▸ heq)).elim⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, fY⟩ ⟨_, hY', fY'⟩
    refine ⟨hX, O_inter_mem hY hY', ?_⟩
    intro h
    rcases O_mem.mp hY with rfl | rfl
    · rw [Set.univ_inter] at h; exact fY' h
    · exact fY rfl
  mono := by
    rintro X X' Y Y' ⟨hX, _, fY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', hY', ?_⟩
    intro hY'eq
    have hYeq : Y = ∅ := Set.subset_empty_iff.mp (hY'eq ▸ hYY')
    obtain ⟨hX0, hmem⟩ := fY hYeq
    have hmem' : V.principal hX ∈ U := hmem
    have hle : V.principal hX ≤ V.principal hX' := (V.principal_le_iff hX hX').mpr hX'X
    exact ⟨hX', V.isOpen_isUpperSet hU hmem' hle⟩

end DomainTheory.NeighbourhoodSystems.Exercise215
