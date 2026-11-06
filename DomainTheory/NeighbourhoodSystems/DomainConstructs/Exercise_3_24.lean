module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.funSpaceIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
set_option linter.unusedVariables false

theorem example_324.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (Sum β γ) V₀
      (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
    (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂))
    (@DomainTheory.NeighbourhoodSystems.funSpace α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
    (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)) :=
  @DomainTheory.NeighbourhoodSystems.funProd_isomorphic
end

section
set_option linter.unusedVariables false

theorem example_324_iter.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (Prod Nat β) V₀
      (@DomainTheory.NeighbourhoodSystems.iterSys β V₁))
    (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
    (@DomainTheory.NeighbourhoodSystems.funSpace α (Prod Nat β) V₀ (@DomainTheory.NeighbourhoodSystems.iterSys β V₁))
    (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)) :=
  @DomainTheory.NeighbourhoodSystems.funIter_isomorphic
end

section
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
end

end DomainTheory.NeighbourhoodSystems
end
