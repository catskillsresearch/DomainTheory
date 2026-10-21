/-ai
If two approximable endomaps a and b agree at bottom, and an approximable endomap f commutes with each of them, then a and b agree at the least fixed point of f. If a predicate on elements holds at bottom, is preserved by the elementwise action of an approximable endomap f, and is closed under suprema of monotone chains, then it holds at the least fixed point of f.

The numbered name example_408 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408.fix_induction_eq
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408.fix_induction

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap

set_option linter.unusedVariables false

theorem example_408.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V a
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V b
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f a)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V a f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f b)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V b f) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V a
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V b
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (P : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V → Prop),
    P (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V) →
      (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          P x → P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x)) →
        (∀ (s : Nat → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (hmono :
              @Monotone Nat (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) Nat.instPreorder
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
                s),
            (∀ (n : Nat), P (s n)) → P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.supChain α V s hmono)) →
          P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V a
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V b
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f a)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V a f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f b)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V b f) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V a
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V b
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (P : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V → Prop),
    P (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V) →
      (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          P x → P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x)) →
        (∀ (s : Nat → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (hmono :
              @Monotone Nat (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) Nat.instPreorder
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
                s),
            (∀ (n : Nat), P (s n)) → P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.supChain α V s hmono)) →
          P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fix_induction_eq
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fix_induction

end DomainTheory.NeighbourhoodSystems.ApproximableMap
