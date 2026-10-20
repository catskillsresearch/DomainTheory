module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem flat_mem {X : Set ℕ} : flat.mem X ↔ X = Set.univ ∨ ∃ n, X = {n} := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise115
