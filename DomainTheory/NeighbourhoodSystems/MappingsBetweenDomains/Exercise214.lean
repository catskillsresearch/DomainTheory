/-ai
If two neighbourhoods are consistent, so that their intersection is a neighbourhood, then phi of the intersection equals the intersection of the two phi values. For a neighbourhood X, the approximable relation of a domain isomorphism holds between X and a set Y exactly when Y is a neighbourhood and the phi-image of X is contained in Y.

The numbered name example_214 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise214.phi_inter
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise214.rel_ofIso_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_214.{u_1, u_2} : And
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X X' : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X)
    (hX' : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X')
    (hXX' :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ (@Inter.inter (Set α) (@Set.instInter α) X X')),
    @Eq (Set β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e (@Inter.inter (Set α) (@Set.instInter α) X X') hXX')
      (@Inter.inter (Set β) (@Set.instInter β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX)
        (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X' hX')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X) {Y : Set β},
    Iff
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β V₀ V₁ e) X Y)
      (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y)
        (@LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX) Y))) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X X' : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X)
    (hX' : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X')
    (hXX' :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ (@Inter.inter (Set α) (@Set.instInter α) X X')),
    @Eq (Set β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e (@Inter.inter (Set α) (@Set.instInter α) X X') hXX')
      (@Inter.inter (Set β) (@Set.instInter β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX)
        (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X' hX')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X) {Y : Set β},
    Iff
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β V₀ V₁ e) X Y)
      (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y)
        (@LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX) Y)))
  @DomainTheory.NeighbourhoodSystems.phi_inter @DomainTheory.NeighbourhoodSystems.rel_ofIso_iff

end DomainTheory.NeighbourhoodSystems
