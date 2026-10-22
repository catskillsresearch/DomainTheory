module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.fixedPoint_not_unique
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.lfpSet_eq_closure

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise417

set_option linter.unusedVariables false

theorem example_417.{u_1} : And
  (∃ (x : Set Nat) (y : Set Nat),
    And
      (@Eq (Set Nat)
        (@DomainTheory.NeighbourhoodSystems.Exercise417.F Nat Nat.instMonoid
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) x)
        x)
      (And
        (@Eq (Set Nat)
          (@DomainTheory.NeighbourhoodSystems.Exercise417.F Nat Nat.instMonoid
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y)
          y)
        (@Ne (Set Nat) x y)))
  (∀ {S : Type u_1} [inst : Monoid S] (a b : S),
    @Eq (Set S)
      (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet S
        (@DomainTheory.NeighbourhoodSystems.Exercise417.F S inst a b))
      (@SetLike.coe (@Submonoid S (@Monoid.toMulOneClass S inst)) S
        (@Submonoid.instSetLike S (@Monoid.toMulOneClass S inst))
        (@Submonoid.closure S (@Monoid.toMulOneClass S inst)
          (@Insert.insert S (Set S) (@Set.instInsert S) a
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) b))))) :=
  @And.intro
  (∃ (x : Set Nat) (y : Set Nat),
    And
      (@Eq (Set Nat)
        (@DomainTheory.NeighbourhoodSystems.Exercise417.F Nat Nat.instMonoid
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) x)
        x)
      (And
        (@Eq (Set Nat)
          (@DomainTheory.NeighbourhoodSystems.Exercise417.F Nat Nat.instMonoid
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y)
          y)
        (@Ne (Set Nat) x y)))
  (∀ {S : Type u_1} [inst : Monoid S] (a b : S),
    @Eq (Set S)
      (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet S
        (@DomainTheory.NeighbourhoodSystems.Exercise417.F S inst a b))
      (@SetLike.coe (@Submonoid S (@Monoid.toMulOneClass S inst)) S
        (@Submonoid.instSetLike S (@Monoid.toMulOneClass S inst))
        (@Submonoid.closure S (@Monoid.toMulOneClass S inst)
          (@Insert.insert S (Set S) (@Set.instInsert S) a
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) b)))))
  DomainTheory.NeighbourhoodSystems.Exercise417.fixedPoint_not_unique
  @DomainTheory.NeighbourhoodSystems.Exercise417.lfpSet_eq_closure

end DomainTheory.NeighbourhoodSystems.Exercise417
