module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.mem_upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet_injective
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.powerSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.powerSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.toPower
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.ofPower

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.20 (the isomorphism).** `toPower`/`ofPower` are mutually inverse and
preserve/reflect `⊑`, giving `|𝒟| ≃o |𝒟'|`. -/
def powerIso : V.Element ≃o V.powerSystem.Element where
  toFun := V.toPower
  invFun := V.ofPower
  left_inv := by
    intro x
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hW, W', hW', heq⟩
      rw [V.upSet_injective hW (x.sub hW') heq]; exact hW'
    · intro hx
      exact ⟨x.sub hx, W, hx, rfl⟩
  right_inv := by
    intro y
    apply Element.ext
    intro S
    constructor
    · rintro ⟨W, ⟨_, hyW⟩, rfl⟩
      exact hyW
    · intro hyS
      obtain ⟨W, hW, rfl⟩ := y.sub hyS
      exact ⟨W, ⟨hW, hyS⟩, rfl⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hx
      have hmem : (V.toPower x).mem (V.upSet W) := ⟨W, hx, rfl⟩
      obtain ⟨W', hW', heq⟩ := h (V.upSet W) hmem
      rw [V.upSet_injective (x.sub hx) (x'.sub hW') heq]; exact hW'
    · intro h S hS
      obtain ⟨W, hW, rfl⟩ := hS
      exact ⟨W, h W hW, rfl⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
