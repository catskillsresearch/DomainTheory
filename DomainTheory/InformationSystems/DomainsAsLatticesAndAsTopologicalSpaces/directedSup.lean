module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.IsDirected

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def directedSup (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S) :
    sys.Element :=
  sys.familySup S (IsDirected.finitelyConsistent sys S hne hdir)

namespace directedSup

theorem carrier_eq_union (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) :
    (sys.directedSup S hne hdir).carrier = sys.familyUnionCarrier S := by
  let hU := IsDirected.finitelyConsistent sys S hne hdir
  refine Set.Subset.antisymm ?_ (deductiveClosure.subset sys _ hU)
  intro a ha
  obtain ⟨u, huU, hEnt⟩ := (ha : a ∈ (sys.deductiveClosure _ hU).carrier)
  obtain ⟨z, hz, huZ⟩ := IsDirected.exists_mem_of_subset_union sys S hne hdir u huU
  exact ⟨z, hz, z.closed u a huZ hEnt⟩

theorem le (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S)
    {z : sys.Element} (h : ∀ x ∈ S, x ≤ z) : sys.directedSup S hne hdir ≤ z :=
  familySup.le sys S (IsDirected.finitelyConsistent sys S hne hdir) h

theorem le_of_mem (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S)
    {x : sys.Element} (hx : x ∈ S) : x ≤ sys.directedSup S hne hdir :=
  familySup.le_of_mem sys S (IsDirected.finitelyConsistent sys S hne hdir) hx

end directedSup

end InfoSys
end DomainTheory.InformationSystems
