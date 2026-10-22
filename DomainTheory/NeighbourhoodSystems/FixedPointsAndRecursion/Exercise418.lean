module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.element_classification
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.natElem_injective
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.natElem_zero_ne_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.succMap_injective
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.zero_ne_succMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise418

set_option linter.unusedVariables false

theorem example_418 : And
  (And
    (And
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (∀ {n m : Nat},
      @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap
            (DomainTheory.NeighbourhoodSystems.Example43.natElem m)) →
        @Eq Nat n m))
  (∀ (n : Nat),
    @Ne
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Example43.N)
      (DomainTheory.NeighbourhoodSystems.Example43.natElem (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
        DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
        DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))) :=
  @And.intro
  (And
    (And
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (∀ {n m : Nat},
      @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap
            (DomainTheory.NeighbourhoodSystems.Example43.natElem m)) →
        @Eq Nat n m))
  (∀ (n : Nat),
    @Ne
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Example43.N)
      (DomainTheory.NeighbourhoodSystems.Example43.natElem (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
        DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
        DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
  (@And.intro
    (And
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (∀ {n m : Nat},
      @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap
            (DomainTheory.NeighbourhoodSystems.Example43.natElem m)) →
        @Eq Nat n m)
    (@And.intro
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@And.intro
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m)
        DomainTheory.NeighbourhoodSystems.Exercise418.element_classification
        @DomainTheory.NeighbourhoodSystems.Exercise418.natElem_injective)
      DomainTheory.NeighbourhoodSystems.Exercise418.natElem_zero_ne_succ)
    @DomainTheory.NeighbourhoodSystems.Exercise418.succMap_injective)
  DomainTheory.NeighbourhoodSystems.Exercise418.zero_ne_succMap

end DomainTheory.NeighbourhoodSystems.Exercise418
