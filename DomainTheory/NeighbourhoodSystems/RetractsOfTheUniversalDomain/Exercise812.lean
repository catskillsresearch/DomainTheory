/-ai
A set of natural numbers is a neighbourhood of V if and only if it is nonempty and equal to a finite union of residue classes 2^k ℕ + ℓ with ℓ < 2^k.

The numbered name example_812 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_mem_iff_finiteUnion

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812 : ∀ {X : Set Nat},
  Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Nat DomainTheory.NeighbourhoodSystems.V X)
    (∃ (F : Finset (Prod Nat Nat)),
      And
        (∀ (p : Prod Nat Nat),
          @Membership.mem (Prod Nat Nat) (Finset (Prod Nat Nat))
              (@SetLike.instMembership (Finset (Prod Nat Nat)) (Prod Nat Nat) (@Finset.instSetLike (Prod Nat Nat))) F
              p →
            @LT.lt Nat instLTNat (@Prod.snd Nat Nat p)
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Prod.fst Nat Nat p)))
        (And
          (@Eq (Set Nat) X
            (⋃ (p : Prod Nat Nat),
              ⋃ (_ :
                @Membership.mem (Prod Nat Nat) (Finset (Prod Nat Nat))
                  (@SetLike.instMembership (Finset (Prod Nat Nat)) (Prod Nat Nat) (@Finset.instSetLike (Prod Nat Nat)))
                  F p),
                DomainTheory.NeighbourhoodSystems.affine (@Prod.fst Nat Nat p) (@Prod.snd Nat Nat p)))
          (@Set.Nonempty Nat X))) :=
  @DomainTheory.NeighbourhoodSystems.V_mem_iff_finiteUnion

end DomainTheory.NeighbourhoodSystems
