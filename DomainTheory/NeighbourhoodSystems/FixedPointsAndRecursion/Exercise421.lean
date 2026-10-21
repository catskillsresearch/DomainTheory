/-ai
A function from naturals to sets of naturals that sends zero to every natural and sends m + 1 to the successor image of its value at m is equal to the up-set function. Any fixed point of Scott's operator on subsets of pairs of naturals equals the order relation. The order relation is a fixed point of Scott's operator on subsets of pairs of naturals. The least fixed point of the multiplication operator of n is the set of multiples of n.

The numbered name example_421 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.upSet_unique
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.leOp_unique
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.leRel_isFixed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.mulOp_lfp_eq_multiples

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise421

set_option linter.unusedVariables false

theorem example_421 : And
  (And
    (And
      (∀ (s : Nat → Set Nat),
        @Eq (Set Nat) (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.univ Nat) →
          (∀ (m : Nat),
              @Eq (Set Nat)
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (DomainTheory.NeighbourhoodSystems.Exercise421.succImage (s m))) →
            @Eq (Nat → Set Nat) s DomainTheory.NeighbourhoodSystems.Exercise421.upSet)
      (∀ {u : Set (Prod Nat Nat)},
        @Eq (Set (Prod Nat Nat)) (DomainTheory.NeighbourhoodSystems.Exercise421.leOp u) u →
          @Eq (Set (Prod Nat Nat)) u DomainTheory.NeighbourhoodSystems.Exercise421.leRel))
    (@Eq (Set (Prod Nat Nat))
      (DomainTheory.NeighbourhoodSystems.Exercise421.leOp DomainTheory.NeighbourhoodSystems.Exercise421.leRel)
      DomainTheory.NeighbourhoodSystems.Exercise421.leRel))
  (∀ (n : Nat),
    @Eq (Set Nat)
      (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet Nat
        (DomainTheory.NeighbourhoodSystems.Exercise421.mulOp n))
      (@Set.ofPred Nat fun (k : Nat) => ∃ (i : Nat), @Eq Nat k (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n i))) :=
  @And.intro
  (And
    (And
      (∀ (s : Nat → Set Nat),
        @Eq (Set Nat) (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.univ Nat) →
          (∀ (m : Nat),
              @Eq (Set Nat)
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (DomainTheory.NeighbourhoodSystems.Exercise421.succImage (s m))) →
            @Eq (Nat → Set Nat) s DomainTheory.NeighbourhoodSystems.Exercise421.upSet)
      (∀ {u : Set (Prod Nat Nat)},
        @Eq (Set (Prod Nat Nat)) (DomainTheory.NeighbourhoodSystems.Exercise421.leOp u) u →
          @Eq (Set (Prod Nat Nat)) u DomainTheory.NeighbourhoodSystems.Exercise421.leRel))
    (@Eq (Set (Prod Nat Nat))
      (DomainTheory.NeighbourhoodSystems.Exercise421.leOp DomainTheory.NeighbourhoodSystems.Exercise421.leRel)
      DomainTheory.NeighbourhoodSystems.Exercise421.leRel))
  (∀ (n : Nat),
    @Eq (Set Nat)
      (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet Nat
        (DomainTheory.NeighbourhoodSystems.Exercise421.mulOp n))
      (@Set.ofPred Nat fun (k : Nat) => ∃ (i : Nat), @Eq Nat k (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n i)))
  (@And.intro
    (And
      (∀ (s : Nat → Set Nat),
        @Eq (Set Nat) (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.univ Nat) →
          (∀ (m : Nat),
              @Eq (Set Nat)
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (DomainTheory.NeighbourhoodSystems.Exercise421.succImage (s m))) →
            @Eq (Nat → Set Nat) s DomainTheory.NeighbourhoodSystems.Exercise421.upSet)
      (∀ {u : Set (Prod Nat Nat)},
        @Eq (Set (Prod Nat Nat)) (DomainTheory.NeighbourhoodSystems.Exercise421.leOp u) u →
          @Eq (Set (Prod Nat Nat)) u DomainTheory.NeighbourhoodSystems.Exercise421.leRel))
    (@Eq (Set (Prod Nat Nat))
      (DomainTheory.NeighbourhoodSystems.Exercise421.leOp DomainTheory.NeighbourhoodSystems.Exercise421.leRel)
      DomainTheory.NeighbourhoodSystems.Exercise421.leRel)
    (@And.intro
      (∀ (s : Nat → Set Nat),
        @Eq (Set Nat) (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.univ Nat) →
          (∀ (m : Nat),
              @Eq (Set Nat)
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (DomainTheory.NeighbourhoodSystems.Exercise421.succImage (s m))) →
            @Eq (Nat → Set Nat) s DomainTheory.NeighbourhoodSystems.Exercise421.upSet)
      (∀ {u : Set (Prod Nat Nat)},
        @Eq (Set (Prod Nat Nat)) (DomainTheory.NeighbourhoodSystems.Exercise421.leOp u) u →
          @Eq (Set (Prod Nat Nat)) u DomainTheory.NeighbourhoodSystems.Exercise421.leRel)
      DomainTheory.NeighbourhoodSystems.Exercise421.upSet_unique
      @DomainTheory.NeighbourhoodSystems.Exercise421.leOp_unique)
    DomainTheory.NeighbourhoodSystems.Exercise421.leRel_isFixed)
  DomainTheory.NeighbourhoodSystems.Exercise421.mulOp_lfp_eq_multiples

end DomainTheory.NeighbourhoodSystems.Exercise421
