module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.Tok
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.a
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.b
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.memSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem

@[expose] public section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_iff (X : Set Tok) : mem X ↔ X = master ∨ X = a ∨ X = b := by
  simp only [mem, memSet, Set.mem_insert_iff, Set.mem_singleton_iff]

end DomainTheory.NeighbourhoodSystems.Exercise119
