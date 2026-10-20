module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.ofExcluded

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

@[simp] theorem mem_ofExcluded {E Y : Set ℕ} :
    (ofExcluded E).mem Y ↔ Yᶜ.Finite ∧ Yᶜ ⊆ E := Iff.rfl

end Cofinite

end DomainTheory.NeighbourhoodSystems
