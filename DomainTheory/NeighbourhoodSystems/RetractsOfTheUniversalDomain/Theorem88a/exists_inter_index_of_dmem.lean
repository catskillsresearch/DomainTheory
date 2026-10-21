/-ai
If the intersection of e i and e j belongs to D, then some index m satisfies both e i ∩ e j = e m and Yidx e i ∩ Yidx e j = Yidx e m.

The covering names such an m on the D side. The index-set form of that equation, rewritten by the intersection rule for index sets, transfers across the splitting to the same equation for the Yidx neighbourhoods. Every index set is contained in the universe, so the side conditions of the transfer hold.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.mem_idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_inter_of_inter_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.univ_nonempty_nat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Subsystemu2etrianglelefteq
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Subsystem

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover in
/-- **The shared "find a matching index" step.** Given `D.mem (e i ∩ e j)` (however that was
established — a direct witness, or `D`'s own `inter_mem`), `hcover` names it as `e m` for some
`m`, and `transfer_inter_eq_iff` (fed through the `idxSet`-level rewriting
`idxSet_inter_of_inter_eq`) pushes the equation across to `Yidx`. This single lemma drives
`DprimeU`'s `inter_mem`, `DprimeU_subsystem`'s `inter_closed`, and both halves of the element-level
isomorphism below. -/
theorem exists_inter_index_of_dmem {i j : ℕ} (hDij : D.mem (e i ∩ e j)) :
    ∃ m, e i ∩ e j = e m ∧ Yidx e i ∩ Yidx e j = Yidx e m := by
  obtain ⟨m, hm⟩ := (hcover (e i ∩ e j)).mp hDij
  exact ⟨m, hm, (transfer_inter_eq_iff splitChoice (idxSet e) Set.univ univ_nonempty_nat
    splitChoice_isSplitSpec i j m
    (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _)).mp (idxSet_inter_of_inter_eq e hm)⟩

end Subsystem

end DomainTheory.NeighbourhoodSystems
