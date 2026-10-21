/-ai
The element map of a product of approximable maps sends a paired element to the pair of the images of the two factors. The element map of a product of approximable maps sends a product element to the pair of the images of its two components.

The numbered name example_319 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.toElementMap_prodMap_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.toElementMap_prodMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_319.{u_1, u_2, u_4, u_5} : And
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g y)))
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (w :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g) w)
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.fst α β V₀ V₁ w))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.snd α β V₀ V₁ w)))) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g y)))
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (w :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g) w)
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.fst α β V₀ V₁ w))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.snd α β V₀ V₁ w))))
  @DomainTheory.NeighbourhoodSystems.toElementMap_prodMap_pair @DomainTheory.NeighbourhoodSystems.toElementMap_prodMap

end DomainTheory.NeighbourhoodSystems
