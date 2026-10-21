/-ai
The embedded neighbourhood system is a subsystem of U.

The master neighbourhoods agree. A member is an embedded set, which is a neighbourhood of U. If the intersection of two embedded sets is a neighbourhood of U, its nonemptiness supplies an intersection index whose embedded set equals the intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.mem_idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.exists_inter_index_of_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.DprimeU

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Subsystemu2etrianglelefteq
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Subsystem

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover he0 in
/-- **`D' ◁ U`.** `sub` is `Yidx_mem`; `inter_closed` uses `exists_inter_index_of_nonempty` to find
*some* witnessed-consistent pair on the `D`-side from the mere non-emptiness of `Yidx e i ∩ Yidx e
j` (guaranteed by `U.mem`). -/
theorem DprimeU_subsystem : DprimeU D e hcover he0 ◁ U where
  master_eq := rfl
  sub := by rintro Y ⟨n, rfl⟩; exact Yidx_mem e n
  inter_closed := by
    rintro X Y ⟨i, rfl⟩ ⟨j, rfl⟩ hUmem
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_nonempty D e hcover hUmem.2.1
    exact ⟨m, hYeq⟩

end Subsystem

end DomainTheory.NeighbourhoodSystems
