module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copairProj_copair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair_comp_inMapu2080
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair_comp_inMapu2081

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_324_distrib.{u_1, u_2, u_3} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq
        (Prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂))
        (@DomainTheory.NeighbourhoodSystems.copairProj α β γ V₀ V₁ V₂ h₀ h₁
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b))
        (@Prod.mk (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) a b))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) γ V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₂
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
        a))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
    (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) γ V₁
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₂
        (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b)
        (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁))
      b) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq
        (Prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂))
        (@DomainTheory.NeighbourhoodSystems.copairProj α β γ V₀ V₁ V₂ h₀ h₁
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b))
        (@Prod.mk (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) a b))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) γ V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₂
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
        a))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
    (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) γ V₁
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₂
        (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b)
        (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁))
      b)
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq
        (Prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂))
        (@DomainTheory.NeighbourhoodSystems.copairProj α β γ V₀ V₁ V₂ h₀ h₁
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b))
        (@Prod.mk (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) a b))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) γ V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₂
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
        a)
    @DomainTheory.NeighbourhoodSystems.copairProj_copair @DomainTheory.NeighbourhoodSystems.copair_comp_inMap₀)
  @DomainTheory.NeighbourhoodSystems.copair_comp_inMap₁

end DomainTheory.NeighbourhoodSystems
