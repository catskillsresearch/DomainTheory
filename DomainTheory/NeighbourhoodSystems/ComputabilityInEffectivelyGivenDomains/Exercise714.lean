/-ai
A nonempty recursively enumerable set of natural numbers is the range of a primitive-recursive function.

The numbered name example_714 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise714

set_option linter.unusedVariables false

theorem example_714.{u_1} : ∀ {β : Type u_1} {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
  {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W},
  @DomainTheory.NeighbourhoodSystems.ComputableElement β W Q y →
    ∃ (t : Nat → Nat),
      And (Nat.Primrec t)
        (And
          (∀ (i : Nat),
            @LE.le (Set β) (@Set.instLE β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q
                (t
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q (t i)))
          (∀ (Z : Set β),
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β W y Z)
              (∃ (i : Nat),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β W
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal β W
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q (t i))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.mem_X β W Q (t i)))
                  Z))) :=
  @DomainTheory.NeighbourhoodSystems.Exercise714.computableElement_eq_decreasing_iUnion_principal

end DomainTheory.NeighbourhoodSystems.Exercise714
