/-ai
Iterated halving is primitive recursive. On a paired code it divides the first component by two raised to the second component, by repeating division by two.

Halving the inner second component is primitive recursive, by composing the primitive-recursive half with the right projection twice. Primitive recursion from the identity with that step is primitive recursive. Unfolding the iterated division and simplifying the pairing identities shows that this recursion is the iterated division.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myDivPow2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_myDivPow2 : Nat.Primrec (fun t => myDivPow2 t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2 / 2) :=
    primrec_div2.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  refine (Nat.Primrec.prec Nat.Primrec.id hg).of_eq fun t => ?_
  unfold myDivPow2
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]

end DomainTheory.NeighbourhoodSystems
