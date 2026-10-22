module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.continuous_toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.mem_iff_principal_of_continuous
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.toElementMap_ofContinuous

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_213.{u, u_1} : And
  (And
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁),
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁)
        fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) =>
        @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁ f x)
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {c :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁},
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) {Y : Set β},
          Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁ (c x) Y)
            (∃ (X : Set α) (hx : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V₀ x X),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁
                (c
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V₀ X
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.sub α V₀ x X hx)))
                Y)))
  (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (c :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
    (hc :
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofContinuous α β V₀ V₁ c hc) x)
      (c x)) :=
  @And.intro
  (And
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁),
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁)
        fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) =>
        @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁ f x)
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {c :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁},
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) {Y : Set β},
          Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁ (c x) Y)
            (∃ (X : Set α) (hx : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V₀ x X),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁
                (c
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V₀ X
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.sub α V₀ x X hx)))
                Y)))
  (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (c :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
    (hc :
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofContinuous α β V₀ V₁ c hc) x)
      (c x))
  (@And.intro
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁),
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁)
        fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) =>
        @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁ f x)
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {c :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁},
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) {Y : Set β},
          Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁ (c x) Y)
            (∃ (X : Set α) (hx : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V₀ x X),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁
                (c
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V₀ X
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.sub α V₀ x X hx)))
                Y))
    @DomainTheory.NeighbourhoodSystems.ApproximableMap.continuous_toElementMap
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem_iff_principal_of_continuous)
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap_ofContinuous

end DomainTheory.NeighbourhoodSystems
