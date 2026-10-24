module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_15

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_13

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
section
variable {α : Type*} {V : NeighborhoodSystem α}
namespace NeighborhoodSystem

/- concordance: source L2293 EXERCISE 4.16 optimal fixed point -/
/-- **Exercise 4.16 (Scott 1981, PRG-19).** The *optimal* fixed point associated with a non-empty
set `S` of fixed points: the least fixed point sitting below `⋂S` (Exercise 4.13(1) applied to the
pre-fixed point `⋂S`). -/
def optimalFix (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element) (hS : S.Nonempty)
    (hfix : ∀ s ∈ S, f s = s) : V.Element :=
  monoFix f (f_sInf_le f hf S hS hfix)

/-- `optimalFix S` is a fixed point. -/
theorem optimalFix_isFixed (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    f (optimalFix f hf S hS hfix) = optimalFix f hf S hS hfix :=
  monoFix_isFixed f hf _

/-- `optimalFix S ⊑ ⋂S`. -/
theorem optimalFix_le_sInf (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    optimalFix f hf S hS hfix ≤ V.sInf S hS :=
  monoFix_le f _

/-- **Exercise 4.16 (Scott 1981, PRG-19).** `optimalFix S` lies below every member of `S`. -/
theorem optimalFix_le (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) {s : V.Element} (hs : s ∈ S) :
    optimalFix f hf S hS hfix ≤ s :=
  le_trans (optimalFix_le_sInf f hf S hS hfix) (V.sInf_le S hS hs)

/-- **Exercise 4.16 (Scott 1981, PRG-19).** `optimalFix S` is *consistent* with every member of `S`
(they share a common upper bound, namely `s` itself). -/
theorem optimalFix_consistent (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) {s : V.Element} (hs : s ∈ S) :
    ∃ ub, optimalFix f hf S hS hfix ≤ ub ∧ s ≤ ub :=
  ⟨s, optimalFix_le f hf S hS hfix hs, le_refl s⟩

end NeighborhoodSystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section
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
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
end
