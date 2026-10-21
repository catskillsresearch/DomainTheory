/-ai
The closure of a consistent finite set is compact: if it lies below the directed supremum of a nonempty directed family, then it lies below some member of that family.

The finite set is contained in the supremum, hence in the union of the carriers. Some member of the family contains the whole finite set, and the closure of a consistent set contained in an element lies below that element.
ai-/

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- Compactness of finite elements: if `ū ≤ ⊔ S` for directed nonempty `S`, then
`ū ≤` some member of `S`. -/
theorem compact_closure (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S)
    {u : Finset α} (hu : u ∈ sys.Con)
    (hle : sys.closure u hu ≤ sys.directedSup S hne hdir) :
    ∃ z ∈ S, sys.closure u hu ≤ z := by
  have huU : (u : Set α) ⊆ sys.familyUnionCarrier S := by
    intro a ha
    have : a ∈ (sys.directedSup S hne hdir).carrier :=
      hle (sys.subset_closure hu (Finset.mem_coe.2 ha))
    rwa [sys.directedSup_carrier_eq_union S hne hdir] at this
  obtain ⟨z, hz, huZ⟩ := sys.exists_mem_of_subset_directedUnion S hne hdir u huU
  exact ⟨z, hz, sys.closure_le_element z hu huZ⟩

end InfoSys
end DomainTheory.InformationSystems
