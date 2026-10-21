/-ai
The product D0 × D1 is isomorphic to D1 × D0. If two domains are isomorphic to two others, then their products are isomorphic. The product D0 × (D1 × D2) is isomorphic to (D0 × D1) × D2.

The numbered name example_315 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prod_comm_isomorphic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.Isomorphicu2eprod
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prod_assoc_isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_315.{u_1, u_2, u_4, u_5, u_3} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α (Sum β γ)) (Sum (Sum α β) γ)
      (@DomainTheory.NeighbourhoodSystems.prod α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
      (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α (Sum β γ)) (Sum (Sum α β) γ)
      (@DomainTheory.NeighbourhoodSystems.prod α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
      (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
    @DomainTheory.NeighbourhoodSystems.prod_comm_isomorphic @DomainTheory.NeighbourhoodSystems.Isomorphic.prod)
  @DomainTheory.NeighbourhoodSystems.prod_assoc_isomorphic

end DomainTheory.NeighbourhoodSystems
