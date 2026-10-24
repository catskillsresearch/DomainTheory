module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_25

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
/- concordance: source L4207 EXERCISE 6.28 finite embeddings cancel -/
/-- **Exercise 6.28 (core).** If `|D|` and `|E|` are finite and `D ⊴ E ⊴ D`, then `D ≅ᴰ E`.
The two `⊴`s give mutual order embeddings of the (finite) element domains, and
`orderIso_of_embeddings` upgrades them to an isomorphism. -/
theorem isomorphic_of_trianglelefteq_both [Finite D.Element] [Finite E.Element]
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  obtain ⟨f⟩ := h₁.elementEmbedding
  obtain ⟨g⟩ := h₂.elementEmbedding
  exact orderIso_of_embeddings f g
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Exercise 6.28 (Scott 1981, PRG-19; suggested by G. Plotkin).** If `𝒟` and `ℰ` are *finite*
neighbourhood systems with `𝒟 ⊴ ℰ` and `ℰ ⊴ 𝒟`, then `𝒟 ≅ ℰ`. -/
theorem isomorphic_of_finite_system (hD : D.IsFinite) (hE : E.IsFinite)
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  have := finite_element_of_isFinite hD
  have := finite_element_of_isFinite hE
  exact isomorphic_of_trianglelefteq_both h₁ h₂
end

section
set_option linter.unusedVariables false

theorem example_628.{u_1, u_2} : And
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite α D →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite β E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D →
            @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E)
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)]
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β E)],
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D → @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite α D →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite β E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D →
            @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E)
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)]
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β E)],
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D → @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E)
  @DomainTheory.NeighbourhoodSystems.isomorphic_of_finite_system
  @DomainTheory.NeighbourhoodSystems.isomorphic_of_trianglelefteq_both
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **Proposition 6.12 (Scott 1981, PRG-19).** Every subdomain relation `D ◁ E` gives rise to a
projection pair `i : D → E`, `j : E → D` with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`. -/
def projectionPair (h : D ◁ E) : ProjectionPair D E where
  inj := h.inj
  proj := h.proj
  proj_comp_inj := h.proj_comp_inj
  inj_comp_proj_le := h.inj_comp_proj_le

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **Element-wise description of `i` (Scott's equation).** `i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}`. -/
theorem toElementMap_inj (h : D ◁ E) (x : D.Element) {Y : Set α} :
    (h.inj.toElementMap x).mem Y ↔ E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y := by
  constructor
  · rintro ⟨X, hX, _, hY, hXY⟩
    exact ⟨hY, X, hX, hXY⟩
  · rintro ⟨hY, X, hX, hXY⟩
    exact ⟨X, hX, x.sub hX, hY, hXY⟩

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **Element-wise description of `j` (Scott's equation).** `j(y) = y ∩ D`: the neighbourhoods of
`j(y)` are exactly the `D`-neighbourhoods that already belong to `y`. -/
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

section
-- Endofunctor.lean
universe u

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

end DomainTheory.NeighbourhoodSystems
end
