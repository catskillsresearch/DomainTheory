/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Finset.Fold
import all Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.interOf_subset_nbhd
public import DomainTheory.BridgeTheorems.toInfoSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

/-- InfoSys element → filter (upward closure of its coded neighbourhoods). -/
def ofElement (e : B.toInfoSys.Element) : B.system.Element where
  mem X := B.system.mem X ∧ ∃ i ∈ e.carrier, B.nbhd i ⊆ X
  sub h := h.1
  master_mem := by
    refine ⟨B.system.master_mem, B.botIdx, ?_, by rw [B.botIdx_eq]⟩
    have hEnt : B.toInfoSys.Ent ∅ B.botIdx := B.toInfoSys.ent_bot (InfoSys.con_empty _)
    exact e.closed ∅ B.botIdx (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
  inter_mem := by
    intro X Y ⟨hX, i, hi, hix⟩ ⟨hY, j, hj, hjy⟩
    have hCon : ({i, j} : Finset ι) ∈ B.toInfoSys.Con :=
      e.consistent {i, j} (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · have : x = j := Finset.mem_singleton.mp hx
          exact this ▸ hj)
    have hInterMem : B.system.mem (B.interOf ({i, j} : Finset ι)) := hCon
    have hInterSub : B.interOf ({i, j} : Finset ι) ⊆ X ∩ Y := by
      intro x hx
      refine ⟨hix (B.interOf_subset_nbhd (by simp) hx),
        hjy (B.interOf_subset_nbhd (by simp) hx)⟩
    refine ⟨B.system.inter_mem hX hY hInterMem hInterSub, ?_⟩
    obtain ⟨k, hk⟩ := B.exhaustive hInterMem
    refine ⟨k, ?_, ?_⟩
    · have hEnt : B.toInfoSys.Ent {i, j} k := ⟨hInterMem, fun x hx => hk ▸ hx⟩
      exact e.closed {i, j} k (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · exact Finset.mem_singleton.mp hx ▸ hj) hEnt
    · intro x hx
      exact hInterSub (hk ▸ hx)
  up_mem := by
    intro X Y ⟨hX, i, hi, hix⟩ hY hXY
    exact ⟨hY, i, hi, hix.trans hXY⟩

end NbhdBasis

end DomainTheory.BridgeTheorems
