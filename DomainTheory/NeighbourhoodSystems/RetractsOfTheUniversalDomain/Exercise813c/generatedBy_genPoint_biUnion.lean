module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_genPoint_box

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems








/-- Finite unions of `box`es (over any index type) are `GeneratedBy genPoint` — the same
`Finset.induction_on`/`Finset.set_biUnion_insert` idiom as `8.13(a)`'s `generatedBy_biUnion_affine`. -/
theorem generatedBy_genPoint_biUnion {β : Type*} (t : Finset β) (I : β → Finset ℕ)
    (f : β → ℕ → Bool) : GeneratedBy genPoint (⋃ b ∈ t, box (I b) (f b)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using generatedBy_genPoint_empty
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (generatedBy_genPoint_box _ _).union ih

end DomainTheory.NeighbourhoodSystems
