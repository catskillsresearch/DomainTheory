/-ai
The infimum of the pre-fixed points of a monotone endomap f is a fixed point of f. For any set, any chosen element, and any unary operation, there is a unique function from the natural numbers that sends zero to the chosen element and sends each successor to the operation applied to the value at the predecessor. The infimum of the pre-fixed points of f is the least fixed point: it lies below every fixed point. The unique function on the natural numbers that sends zero to zero and commutes with successor is the identity.

The numbered name example_413 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.monoFix_isFixed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.exists_unique_nat_rec
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.monoFix_least
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.nat_iterate_unique

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_413.{u_1, u_2} : And
  (And
    (And
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n)))))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
      (ha :
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (f a) a)
      {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha) y))
  (∀ {s : Nat → Nat},
    @Eq Nat (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      (∀ (n : Nat),
          @Eq Nat
            (s
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (s n)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        ∀ (n : Nat), @Eq Nat (s n) n) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n)))))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
      (ha :
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (f a) a)
      {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha) y))
  (∀ {s : Nat → Nat},
    @Eq Nat (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      (∀ (n : Nat),
          @Eq Nat
            (s
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (s n)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        ∀ (n : Nat), @Eq Nat (s n) n)
  (@And.intro
    (And
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n)))))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
      (ha :
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (f a) a)
      {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha) y)
    (@And.intro
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n))))
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix_isFixed
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.exists_unique_nat_rec)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix_least)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.nat_iterate_unique

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
