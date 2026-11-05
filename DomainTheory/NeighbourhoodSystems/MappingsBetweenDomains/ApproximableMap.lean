module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
variable {α β γ δ : Type*}

structure ApproximableMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) where

  rel : Set α → Set β → Prop

  rel_dom : ∀ {X Y}, rel X Y → V₀.mem X

  rel_cod : ∀ {X Y}, rel X Y → V₁.mem Y

  master_rel : rel V₀.master V₁.master

  inter_right : ∀ {X Y Y'}, rel X Y → rel X Y' → rel X (Y ∩ Y')

  mono : ∀ {X X' Y Y'}, rel X Y → X' ⊆ X → Y ⊆ Y' → V₀.mem X' → V₁.mem Y' → rel X' Y'

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

theorem ext {f g : ApproximableMap V₀ V₁} (h : ∀ X Y, f.rel X Y ↔ g.rel X Y) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y; exact propext (h X Y)
  subst this; rfl

def toElementMap (f : ApproximableMap V₀ V₁) (x : V₀.Element) : V₁.Element where
  mem Y := ∃ X, x.mem X ∧ f.rel X Y
  sub := fun ⟨_, _, hXY⟩ => f.rel_cod hXY
  master_mem := ⟨V₀.master, x.master_mem, f.master_rel⟩
  inter_mem := by
    rintro Y Y' ⟨X, hX, hXY⟩ ⟨X', hX', hX'Y'⟩
    have hXX'mem : x.mem (X ∩ X') := x.inter_mem hX hX'
    have hXX' : V₀.mem (X ∩ X') := x.sub hXX'mem
    refine ⟨X ∩ X', hXX'mem, ?_⟩
    have h1 : f.rel (X ∩ X') Y :=
      f.mono hXY Set.inter_subset_left subset_rfl hXX' (f.rel_cod hXY)
    have h2 : f.rel (X ∩ X') Y' :=
      f.mono hX'Y' Set.inter_subset_right subset_rfl hXX' (f.rel_cod hX'Y')
    exact f.inter_right h1 h2
  up_mem := by
    rintro Y Y' ⟨X, hX, hXY⟩ hY' hYY'
    exact ⟨X, hX, f.mono hXY subset_rfl hYY' (x.sub hX) hY'⟩

@[simp] theorem mem_toElementMap (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β} :
    (f.toElementMap x).mem Y ↔ ∃ X, x.mem X ∧ f.rel X Y := Iff.rfl

theorem rel_iff_mem_principal (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) {Y : Set β} :
    f.rel X Y ↔ (f.toElementMap (V₀.principal hX)).mem Y := by
  constructor
  · intro hXY
    exact ⟨X, ⟨hX, subset_rfl⟩, hXY⟩
  · rintro ⟨Z, ⟨_, hXZ⟩, hZY⟩
    exact f.mono hZY hXZ subset_rfl hX (f.rel_cod hZY)

theorem ext_of_toElementMap {f g : ApproximableMap V₀ V₁}
    (h : ∀ x, f.toElementMap x = g.toElementMap x) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : V₀.mem X
  · rw [f.rel_iff_mem_principal hX, g.rel_iff_mem_principal hX, h]
  · constructor
    · intro hr; exact absurd (f.rel_dom hr) hX
    · intro hr; exact absurd (g.rel_dom hr) hX

theorem rel_master (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) :
    f.rel X V₁.master :=
  f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem

theorem toElementMap_mono (f : ApproximableMap V₀ V₁) {x y : V₀.Element} (hxy : x ≤ y) :
    f.toElementMap x ≤ f.toElementMap y := by
  rintro Y ⟨X, hX, hXY⟩
  exact ⟨X, hxy X hX, hXY⟩

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
