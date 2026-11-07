module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.projPairSubdomain

public import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

def NeighborhoodSystem.IsFinite {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  Finite {X : Set α // D.mem X}

def projElementEmbedding {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    (i : ApproximableMap D E) (j : ApproximableMap E D) (hji : j.comp i = idMap D) :
    D.Element ↪o E.Element :=
  OrderEmbedding.ofMapLEIff i.toElementMap (by
    have hround : ∀ x : D.Element, j.toElementMap (i.toElementMap x) = x := by
      intro x; rw [← toElementMap_comp, hji, toElementMap_idMap]
    intro a b
    constructor
    · intro h
      have hjm := toElementMap_mono j h
      rwa [hround a, hround b] at hjm
    · intro h
      exact toElementMap_mono i h)

theorem Trianglelefteq.elementEmbedding (h : D ⊴ E) :
    Nonempty (D.Element ↪o E.Element) := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  exact ⟨e.toOrderEmbedding.trans
    (projElementEmbedding hsub.inj hsub.proj hsub.proj_comp_inj)⟩

theorem finite_element_of_isFinite {α : Type*} {D : NeighborhoodSystem α} (h : D.IsFinite) :
    Finite D.Element := by
  have : Finite {X : Set α // D.mem X} := h
  apply Finite.of_injective
    (β := Set {X : Set α // D.mem X}) (fun x => {p | x.mem p.1})
  intro x y hxy
  apply Element.ext
  intro X
  by_cases hX : D.mem X
  · have := Set.ext_iff.mp hxy ⟨X, hX⟩
    simpa using this
  · exact ⟨fun hmem => absurd (x.sub hmem) hX, fun hmem => absurd (y.sub hmem) hX⟩

theorem orderIso_of_embeddings {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    [Finite P] [Finite Q] (f : P ↪o Q) (g : Q ↪o P) : Nonempty (P ≃o Q) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype P
  obtain ⟨_⟩ := nonempty_fintype Q
  have hcard : Fintype.card P = Fintype.card Q :=
    le_antisymm (Fintype.card_le_of_injective f f.injective)
      (Fintype.card_le_of_injective g g.injective)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, hcard⟩
  exact ⟨{ toEquiv := Equiv.ofBijective f hbij, map_rel_iff' := f.map_rel_iff' }⟩

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

namespace Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

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

export CategoryTheory (Category)

open scoped CategoryTheory

universe u

abbrev compAfter {Obj : Type u} [Category.{v} Obj] {X Y Z : Obj} (g : Y ⟶ Z) (f : X ⟶ Y) : X ⟶ Z :=
  f ≫ g

scoped infixr:80 " ⊚ " => compAfter

end DomainTheory.NeighbourhoodSystems
