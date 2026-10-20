module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.generatedBy_affine

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem











theorem generatedBy_biUnion_affine (k : ℕ) (s : Finset ℕ) (hs : ∀ ℓ ∈ s, ℓ < 2 ^ k) :
    GeneratedBy generator (⋃ ℓ ∈ s, affine k ℓ) := by
  induction s using Finset.induction_on with
  | empty => simpa using GeneratedBy.univ.compl
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact GeneratedBy.union (generatedBy_affine k a (hs a (Finset.mem_insert_self a s)))
      (ih fun ℓ hℓ => hs ℓ (Finset.mem_insert_of_mem hℓ))

end DomainTheory.NeighbourhoodSystems
