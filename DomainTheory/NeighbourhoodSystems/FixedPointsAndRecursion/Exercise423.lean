module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise423.f_unique_fixedPoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap

set_option linter.unusedVariables false

theorem example_423.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
  (a : Nat → @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
  (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
          (a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) x)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @IsLUB (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@Set.ofPred (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) =>
            ∃ (n : Nat),
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) y
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V (a n) x))
          x) →
      (∀ (n : Nat) (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
              (a
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
              (a
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V (a n) x)))) →
        @ExistsUnique (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) =>
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x :=
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.f_unique_fixedPoint

end DomainTheory.NeighbourhoodSystems.ApproximableMap
