/-ai
A set of elements is bounded if and only if every finite subset is bounded. For neighbourhoods U and W, the two-term sequence is consistent at length 2 if and only if the set of the two principal filters is bounded. Every member of a bounded set of elements lies below the least upper bound of the set. The least upper bound of a bounded set of elements lies below any element that lies above every member of the set.

The numbered name example_127 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.bounded_iff_finite_bounded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.consistent_pair_iff_bounded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.le_sSup
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.sSup_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_127.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW))))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
      {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          x (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
          @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
            x z) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX) z) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW))))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
      {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          x (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
          @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
            x z) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX) z)
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW))))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
      {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          x (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX))
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW)))))
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bounded_iff_finite_bounded
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.consistent_pair_iff_bounded)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.le_sSup)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup_le

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
