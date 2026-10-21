/-ai
For a nonempty directed family of elements, the carrier of the directed supremum equals the union of the carriers.

Finite consistency of that union is the directed-family lemma. The union is contained in its deductive closure. A token of the deductive closure is entailed by some finite subset of the union, that subset lies in a single member of the family, and that member is closed under the entailment.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- For directed families, the lub carrier equals the raw union (already deductively closed). -/
theorem directedSup_carrier_eq_union (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) :
    (sys.directedSup S hne hdir).carrier = sys.familyUnionCarrier S := by
  let hU := sys.finitelyConsistent_of_directed S hne hdir
  refine Set.Subset.antisymm ?_ (sys.subset_deductiveClosure _ hU)
  intro a ha
  obtain ⟨u, huU, hEnt⟩ := (ha : a ∈ (sys.deductiveClosure _ hU).carrier)
  obtain ⟨z, hz, huZ⟩ := sys.exists_mem_of_subset_directedUnion S hne hdir u huU
  exact ⟨z, hz, z.closed u a huZ hEnt⟩

end InfoSys
end DomainTheory.InformationSystems
