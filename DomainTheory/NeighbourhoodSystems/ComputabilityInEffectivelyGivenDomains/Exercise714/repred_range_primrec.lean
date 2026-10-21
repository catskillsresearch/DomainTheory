/-ai
The range of a primitive-recursive function on the natural numbers is recursively enumerable.

Equality of the value of the function on the first component of a code with the second component is recursively decidable, by composing the function with the first projection and comparing it with the second projection. A number lies in the range exactly when some index forms such a code, by the pairing equations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise714

open NeighborhoodSystem Domain.Recursive DomainTheory.NeighbourhoodSystems


/-- **The range of a primitive recursive function is recursively enumerable.** The relation
`r i = n` is recursively decidable (`RecDecidable.natEq`), and `∃ i, r i = n` is its projection, so
it is r.e. by definition of `REPred`. -/
theorem repred_range_primrec {r : ℕ → ℕ} (hr : Nat.Primrec r) :
    REPred (fun n => ∃ i, r i = n) := by
  refine ⟨fun t => r t.unpair.1 = t.unpair.2,
    RecDecidable.natEq (hr.comp Nat.Primrec.left) Nat.Primrec.right, fun n => ?_⟩
  refine exists_congr (fun i => ?_)
  simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems.Exercise714
