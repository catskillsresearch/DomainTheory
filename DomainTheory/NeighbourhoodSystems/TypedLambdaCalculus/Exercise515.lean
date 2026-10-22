module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.part1
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.park_least
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.park_solves

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise515

set_option linter.unusedVariables false

theorem example_515.{u_1} : And
  (And
    (∀ {S : Type u_1} [inst : Monoid S] (e e' : S),
      @Eq (Set S)
        (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet S fun (w : Set S) =>
          @Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e) w)
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e'))
        (@HMul.hMul (Set S) (Set S) (Set S)
          (@instHMul (Set S) (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
          (@DomainTheory.NeighbourhoodSystems.Exercise515.star S inst
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e))
          (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e')))
    (∀ {S : Type u_1} [inst : Monoid S] (a b c d : Set S) {x y : Set S},
      @Eq (Set S) x
          (@Union.union (Set S) (@Set.instUnion S)
            (@Union.union (Set S) (@Set.instUnion S)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                a x)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                b y))
            c) →
        @Eq (Set S) y
            (@Union.union (Set S) (@Set.instUnion S)
              (@Union.union (Set S) (@Set.instUnion S)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  b x)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  a y))
              d) →
          And (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d) x)
            (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d) y)))
  (∀ {S : Type u_1} [inst : Monoid S] (a b c d : Set S),
    And
      (@Eq (Set S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d)
        (@Union.union (Set S) (@Set.instUnion S)
          (@Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              a (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d))
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              b (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)))
          c))
      (@Eq (Set S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)
        (@Union.union (Set S) (@Set.instUnion S)
          (@Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              b (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d))
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              a (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)))
          d))) :=
  @And.intro
  (And
    (∀ {S : Type u_1} [inst : Monoid S] (e e' : S),
      @Eq (Set S)
        (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet S fun (w : Set S) =>
          @Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e) w)
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e'))
        (@HMul.hMul (Set S) (Set S) (Set S)
          (@instHMul (Set S) (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
          (@DomainTheory.NeighbourhoodSystems.Exercise515.star S inst
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e))
          (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e')))
    (∀ {S : Type u_1} [inst : Monoid S] (a b c d : Set S) {x y : Set S},
      @Eq (Set S) x
          (@Union.union (Set S) (@Set.instUnion S)
            (@Union.union (Set S) (@Set.instUnion S)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                a x)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                b y))
            c) →
        @Eq (Set S) y
            (@Union.union (Set S) (@Set.instUnion S)
              (@Union.union (Set S) (@Set.instUnion S)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  b x)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  a y))
              d) →
          And (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d) x)
            (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d) y)))
  (∀ {S : Type u_1} [inst : Monoid S] (a b c d : Set S),
    And
      (@Eq (Set S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d)
        (@Union.union (Set S) (@Set.instUnion S)
          (@Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              a (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d))
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              b (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)))
          c))
      (@Eq (Set S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)
        (@Union.union (Set S) (@Set.instUnion S)
          (@Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              b (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d))
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              a (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)))
          d)))
  (@And.intro
    (∀ {S : Type u_1} [inst : Monoid S] (e e' : S),
      @Eq (Set S)
        (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet S fun (w : Set S) =>
          @Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e) w)
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e'))
        (@HMul.hMul (Set S) (Set S) (Set S)
          (@instHMul (Set S) (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
          (@DomainTheory.NeighbourhoodSystems.Exercise515.star S inst
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e))
          (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e')))
    (∀ {S : Type u_1} [inst : Monoid S] (a b c d : Set S) {x y : Set S},
      @Eq (Set S) x
          (@Union.union (Set S) (@Set.instUnion S)
            (@Union.union (Set S) (@Set.instUnion S)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                a x)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                b y))
            c) →
        @Eq (Set S) y
            (@Union.union (Set S) (@Set.instUnion S)
              (@Union.union (Set S) (@Set.instUnion S)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  b x)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  a y))
              d) →
          And (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d) x)
            (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d) y))
    @DomainTheory.NeighbourhoodSystems.Exercise515.part1 @DomainTheory.NeighbourhoodSystems.Exercise515.park_least)
  @DomainTheory.NeighbourhoodSystems.Exercise515.park_solves

end DomainTheory.NeighbourhoodSystems.Exercise515
