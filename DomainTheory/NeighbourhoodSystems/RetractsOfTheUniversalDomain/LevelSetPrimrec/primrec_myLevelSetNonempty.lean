/-ai
The bounded search for a nonempty level set is primitive recursive. On a paired code it asks whether the nonempty-body test succeeds for some value below two to the power of the first component, searching through the second component.

Bounded existential quantification of the primitive-recursive body is primitive recursive, and so is two to the power of the left component. Composing the existential with the pairing of the right projection and that power is primitive recursive. Unfolding the search and the pairing identities shows that this composition is the search.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSetNonemptyBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_levelSetNonemptyBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_myLevelSetNonempty :
    Nat.Primrec (fun t => myLevelSetNonempty t.unpair.1 t.unpair.2) := by
  have hbe : Nat.Primrec (fun t : ℕ => bExistsFn levelSetNonemptyBody t.unpair.1 t.unpair.2) :=
    primrec_bExistsFn primrec_levelSetNonemptyBody
  have hpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.1) := primrec_two_pow Nat.Primrec.left
  exact (hbe.comp (Nat.Primrec.right.pair hpow)).of_eq fun t => by
    simp only [myLevelSetNonempty, unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
