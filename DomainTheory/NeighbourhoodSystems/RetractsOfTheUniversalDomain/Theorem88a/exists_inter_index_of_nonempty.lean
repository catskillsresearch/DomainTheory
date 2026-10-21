/-ai
If Yidx e i ∩ Yidx e j is nonempty, then some index m satisfies both e i ∩ e j = e m and Yidx e i ∩ Yidx e j = Yidx e m.

The intersection of the index sets is nonempty. If it were empty, the transfer of emptiness, after the intersections with the universe are removed, would make the Yidx intersection empty. Any index k in the intersection satisfies e k ⊆ e i ∩ e j, so the intersection law of D puts e i ∩ e j in D, and the witnessed form of the lemma supplies m.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.D_mem_e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.univ_nonempty_nat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.exists_inter_index_of_dmem

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Subsystemu2etrianglelefteq
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Subsystem

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover in
/-- **The "unwitnessed" variant**, used exactly when only the raw non-emptiness of `Yidx e i ∩
Yidx e j` is known (not an explicit `D`-side witness): non-emptiness transfers down
(`transfer_inter_empty_iff`) to `idxSet e i ∩ idxSet e j`, any element `k` of which supplies
`e k ⊆ e i ∩ e j`, so `D`'s own `inter_mem` produces `D.mem (e i ∩ e j)` and
`exists_inter_index_of_dmem` finishes. -/
theorem exists_inter_index_of_nonempty {i j : ℕ} (hne : (Yidx e i ∩ Yidx e j).Nonempty) :
    ∃ m, e i ∩ e j = e m ∧ Yidx e i ∩ Yidx e j = Yidx e m := by
  have hne' : (idxSet e i ∩ idxSet e j).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hkey := transfer_inter_empty_iff splitChoice (idxSet e) Set.univ univ_nonempty_nat
      splitChoice_isSplitSpec i j
    rw [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yidx_subset_master e i)] at hkey
    exact hne.ne_empty (hkey.mp hcon)
  obtain ⟨k, hki, hkj⟩ := hne'
  exact exists_inter_index_of_dmem D e hcover
    (D.inter_mem (D_mem_e D e hcover i) (D_mem_e D e hcover j) (D_mem_e D e hcover k)
      (Set.subset_inter hki hkj))

end Subsystem

end DomainTheory.NeighbourhoodSystems
