/-ai
Composing the left injection, the sum of two approximable maps, and the left projection recovers the first map. Composing the right injection, the sum of two approximable maps, and the right projection recovers the second map.

The numbered name example_319_sum is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.outMapu2080_comp_sumMap_comp_inMapu2080
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.outMapu2081_comp_sumMap_comp_inMapu2081

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_319_sum.{u_1, u_2, u_3, u_4} : And
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α' β')) α' V₀
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₀'
        (@DomainTheory.NeighbourhoodSystems.outMap₀ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) (Option (Sum α' β')) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
      f)
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α' β')) β' V₁
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₁'
        (@DomainTheory.NeighbourhoodSystems.outMap₁ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) (Option (Sum α' β')) V₁
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
      g) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α' β')) α' V₀
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₀'
        (@DomainTheory.NeighbourhoodSystems.outMap₀ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) (Option (Sum α' β')) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
      f)
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α' β')) β' V₁
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₁'
        (@DomainTheory.NeighbourhoodSystems.outMap₁ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) (Option (Sum α' β')) V₁
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
      g)
  @DomainTheory.NeighbourhoodSystems.outMap₀_comp_sumMap_comp_inMap₀
  @DomainTheory.NeighbourhoodSystems.outMap₁_comp_sumMap_comp_inMap₁

end DomainTheory.NeighbourhoodSystems
