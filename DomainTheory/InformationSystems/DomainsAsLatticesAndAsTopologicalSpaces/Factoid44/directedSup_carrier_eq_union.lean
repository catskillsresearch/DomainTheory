/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
