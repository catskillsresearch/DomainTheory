/-ai
For a nonempty set of fixed points of a monotone endomap, the image of the infimum lies below the infimum. The optimal fixed point of a nonempty set of fixed points is consistent with every member of the set: the two elements have a common upper bound. The optimal fixed point of a nonempty set of fixed points lies below every member of the set.

The numbered name example_416 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise416.f_sInf_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise416.optimalFix_consistent
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise416.optimalFix_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_416.{u_1} : And
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
        ∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S),
          (∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
              @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s) →
            @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (hf :
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          f)
      (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S)
      (hfix :
        ∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s)
      {s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
        ∃ (ub : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix α V f hf S hS hfix) ub)
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              s ub)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (hf :
      @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f)
    (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
    (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S)
    (hfix :
      ∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s)
    {s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix α V f hf S hS hfix) s) :=
  @And.intro
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
        ∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S),
          (∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
              @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s) →
            @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (hf :
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          f)
      (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S)
      (hfix :
        ∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s)
      {s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
        ∃ (ub : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix α V f hf S hS hfix) ub)
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              s ub)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (hf :
      @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f)
    (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
    (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S)
    (hfix :
      ∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s)
    {s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix α V f hf S hS hfix) s)
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
        ∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S),
          (∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
              @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s) →
            @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (hf :
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          f)
      (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S)
      (hfix :
        ∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s)
      {s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
        ∃ (ub : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix α V f hf S hS hfix) ub)
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              s ub))
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.f_sInf_le
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix_consistent)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix_le

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
