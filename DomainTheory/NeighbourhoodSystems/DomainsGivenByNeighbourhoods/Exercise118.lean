/-ai
The least filter containing a finitely consistent family approximates every filter that contains the family. The family of the three-token system is not finitely consistent.

The numbered name example_118 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.leastFilter_le
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.not_finitelyConsistent

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_118.{u_1} : And
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (C : Set (Set α))
    (hCsub :
      ∀ (X : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
    (hC : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent α V C)
    (z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    (∀ (W : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C W →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V z W) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.leastFilter α V C hCsub hC) z)
  (Not
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent
      (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) DomainTheory.NeighbourhoodSystems.triSys
      DomainTheory.NeighbourhoodSystems.triSys.family)) :=
  @And.intro
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (C : Set (Set α))
    (hCsub :
      ∀ (X : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
    (hC : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent α V C)
    (z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    (∀ (W : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C W →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V z W) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.leastFilter α V C hCsub hC) z)
  (Not
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent
      (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) DomainTheory.NeighbourhoodSystems.triSys
      DomainTheory.NeighbourhoodSystems.triSys.family))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.leastFilter_le)
  DomainTheory.NeighbourhoodSystems.triSys.not_finitelyConsistent

end DomainTheory.NeighbourhoodSystems
