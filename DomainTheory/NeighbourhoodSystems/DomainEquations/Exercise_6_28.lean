module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_25

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

theorem isomorphic_of_trianglelefteq_both [Finite D.Element] [Finite E.Element]
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  obtain ⟨f⟩ := h₁.elementEmbedding
  obtain ⟨g⟩ := h₂.elementEmbedding
  exact orderIso_of_embeddings f g

theorem isomorphic_of_finite_system (hD : D.IsFinite) (hE : E.IsFinite)
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  have := finite_element_of_isFinite hD
  have := finite_element_of_isFinite hE
  exact isomorphic_of_trianglelefteq_both h₁ h₂

end

section
open NeighborhoodSystem

/-- Scott's Exercise 6.28: mutual embeddings of finite systems yield an isomorphism. -/
theorem example_628 :
    (∀ {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β},
      D.IsFinite → E.IsFinite → D ⊴ E → E ⊴ D → D ≅ᴰ E) ∧
    (∀ {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
      [Finite D.Element] [Finite E.Element],
      D ⊴ E → E ⊴ D → D ≅ᴰ E) :=
  ⟨@isomorphic_of_finite_system, @isomorphic_of_trianglelefteq_both⟩
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

def projectionPair (h : D ◁ E) : ProjectionPair D E where
  inj := h.inj
  proj := h.proj
  proj_comp_inj := h.proj_comp_inj
  inj_comp_proj_le := h.inj_comp_proj_le

theorem toElementMap_inj (h : D ◁ E) (x : D.Element) {Y : Set α} :
    (h.inj.toElementMap x).mem Y ↔ E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y := by
  constructor
  · rintro ⟨X, hX, _, hY, hXY⟩
    exact ⟨hY, X, hX, hXY⟩
  · rintro ⟨hY, X, hX, hXY⟩
    exact ⟨X, hX, x.sub hX, hY, hXY⟩

theorem toElementMap_proj (h : D ◁ E) (y : E.Element) {X : Set α} :
    (h.proj.toElementMap y).mem X ↔ y.mem X ∧ D.mem X := by
  constructor
  · rintro ⟨Y, hY, hEY, hX, hYX⟩
    exact ⟨y.up_mem hY (h.sub hX) hYX, hX⟩
  · rintro ⟨hX, hDX⟩
    exact ⟨X, hX, y.sub hX, hDX, subset_rfl⟩

end Subsystem
end

section
export CategoryTheory (Category)

open scoped CategoryTheory

universe u

abbrev compAfter {Obj : Type u} [Category.{v} Obj] {X Y Z : Obj} (g : Y ⟶ Z) (f : X ⟶ Y) : X ⟶ Z :=
  f ≫ g
end

section
export CategoryTheory (Category)

open scoped CategoryTheory

scoped infixr:80 " ⊚ " => compAfter
end

section
export CategoryTheory (Category)
end

end DomainTheory.NeighbourhoodSystems
end
