module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.outMapu2080_comp_inMapu2080
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.outMapu2081_comp_inMapu2081

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_318.{u_1, u_2} : And
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V₀ V₀)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) α V₀
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
        (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β V₁ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) β V₁
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
        (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap β V₁)) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V₀ V₀)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) α V₀
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
        (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β V₁ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) β V₁
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
        (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap β V₁))
  @DomainTheory.NeighbourhoodSystems.outMap₀_comp_inMap₀ @DomainTheory.NeighbourhoodSystems.outMap₁_comp_inMap₁

end DomainTheory.NeighbourhoodSystems
