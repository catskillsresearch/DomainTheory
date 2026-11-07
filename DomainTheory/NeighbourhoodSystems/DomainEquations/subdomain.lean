module

public import Mathlib.CategoryTheory.Category.Basic

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.DomainObj
public import Mathlib.Tactic.ToAdditive

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
export CategoryTheory (Category)

open scoped CategoryTheory

scoped notation "𝟙" => CategoryTheory.CategoryStruct.id

variable {α : Type*}

structure Subsystem (D E : NeighborhoodSystem α) : Prop where
  master_eq : D.master = E.master
  sub : ∀ {X : Set α}, D.mem X → E.mem X
  inter_closed : ∀ {X Y : Set α}, D.mem X → D.mem Y → E.mem (X ∩ Y) → D.mem (X ∩ Y)

@[inherit_doc] infix:50 " ◁ " => Subsystem

namespace Subsystem

theorem _root_.DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.ext {D E : NeighborhoodSystem α}
    (hmem : ∀ X, D.mem X ↔ E.mem X) (hmaster : D.master = E.master) : D = E := by
  rcases D with ⟨Dmem, Dmaster, _, _, _⟩
  rcases E with ⟨Emem, Emaster, _, _, _⟩
  have hm : Dmem = Emem := funext fun X => propext (hmem X)
  subst hm
  subst hmaster
  rfl

theorem antisymm {D E : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ D) : D = E :=
  NeighborhoodSystem.ext (fun _ => ⟨fun h => h₁.sub h, fun h => h₂.sub h⟩) h₁.master_eq

theorem refl (D : NeighborhoodSystem α) : D ◁ D where
  master_eq := rfl
  sub h := h
  inter_closed _ _ h := h

theorem trans {D E F : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ F) : D ◁ F where
  master_eq := h₁.master_eq.trans h₂.master_eq
  sub h := h₂.sub (h₁.sub h)
  inter_closed hX hY hXY :=
    h₁.inter_closed hX hY (h₂.inter_closed (h₁.sub hX) (h₁.sub hY) hXY)

theorem subsystem_iff_subset_of_common {D₀ D₁ E : NeighborhoodSystem α}
    (h₀ : D₀ ◁ E) (h₁ : D₁ ◁ E) :
    D₀ ◁ D₁ ↔ ∀ {X : Set α}, D₀.mem X → D₁.mem X := by
  constructor
  · intro h _ hX; exact h.sub hX
  · intro hsub
    refine ⟨h₀.master_eq.trans h₁.master_eq.symm, hsub, ?_⟩
    intro X Y hX hY hXY
    exact h₀.inter_closed hX hY (h₁.sub hXY)

end Subsystem

end DomainTheory.NeighbourhoodSystems
