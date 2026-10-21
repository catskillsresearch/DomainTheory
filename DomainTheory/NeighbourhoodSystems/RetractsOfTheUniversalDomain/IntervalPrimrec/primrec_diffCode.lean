/-ai
The map sending a paired natural number to the difference code of its two components is
primitive recursive.

Unfolding the difference code, the swapped application of the difference-all code is
primitive recursive by composing that code with the pairing of the right and left
projections and simplifying the pairing projections. Composing the primitive-recursive
flat-map code of that function with the same swapped pairing, and simplifying again,
matches the unfolded difference code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.primrec_diffAllCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem primrec_diffCode : Nat.Primrec (fun t : ℕ => diffCode t.unpair.1 t.unpair.2) := by
  unfold diffCode
  have hf : Nat.Primrec (fun t : ℕ => diffAllCode t.unpair.2 t.unpair.1) :=
    (primrec_diffAllCode.comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact ((primrec_flatMapCode hf).comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
