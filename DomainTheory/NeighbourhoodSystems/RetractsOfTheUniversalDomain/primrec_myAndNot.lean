/-ai
The function sending a paired natural number to the and-not of its two components is primitive recursive.

The iterative conjunction of the two components is primitive recursive, and the iterative exclusive disjunction of the first component with that conjunction is primitive recursive. Simplifying by the definition of and-not and the pairing projections matches the definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_myXor
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myAndNot

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_myAndNot : Nat.Primrec (fun t => myAndNot t.unpair.1 t.unpair.2) := by
  have hland : Nat.Primrec (fun t : ℕ => myLand t.unpair.1 t.unpair.2) := primrec_myLand
  exact (primrec_myXor.comp (Nat.Primrec.left.pair hland)).of_eq fun t => by
    simp only [myAndNot, unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
