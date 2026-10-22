module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.mem_idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.D_mem_e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.embed_subset_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.exists_inter_index_of_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.DprimeU_subsystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **Pullback**: the `D`-filter `{e n ∣ Yidx e n ∈ y}` induced by a `D'`-filter `y`. -/
def toD (y : (DprimeU D e hcover he0).Element) : D.Element where
  mem S := ∃ n, S = e n ∧ y.mem (Yidx e n)
  sub := fun ⟨n, hn, _⟩ => hn ▸ D_mem_e D e hcover n
  master_mem := ⟨0, he0.symm, by rw [Yidx_zero D e hcover he0]; exact y.master_mem⟩
  inter_mem := by
    rintro S T ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    have hD'mem : (DprimeU D e hcover he0).mem (Yidx e i ∩ Yidx e j) := y.sub (y.inter_mem hyi hyj)
    obtain ⟨m, hem, hYeq⟩ := exists_inter_index_of_nonempty D e hcover
      ((DprimeU_subsystem D e hcover he0).sub hD'mem).2.1
    exact ⟨m, hem, hYeq ▸ y.inter_mem hyi hyj⟩
  up_mem := by
    rintro S T ⟨i, rfl, hyi⟩ hDT hST
    obtain ⟨j, rfl⟩ := (hcover T).mp hDT
    have hYij : Yidx e i ⊆ Yidx e j := (embed_subset_iff e i j).mp hST
    exact ⟨j, rfl, y.up_mem hyi ⟨j, rfl⟩ hYij⟩

end Iso

end DomainTheory.NeighbourhoodSystems
