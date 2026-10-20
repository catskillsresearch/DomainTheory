/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid42

/-!
# Factoid 4.3 — consistent joins

**Factoid 4.3 (Scott §4).** The join of a family of elements exists in `|A|` iff the
union of their carriers is finitely consistent; in that case the join is the deductive
closure of the union. Binary case: `x ⊔ y` exists iff some element bounds both.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- A (possibly infinite) set of tokens is *finitely consistent* when every finite subset
lies in `Con`. -/
def IsFinitelyConsistent (U : Set α) : Prop :=
  ∀ Y : Finset α, (Y : Set α) ⊆ U → Y ∈ sys.Con

/-- Witness: some finite `w ⊆ U` entails every member of `Y ⊆ deductiveClosure U`. -/
theorem exists_entSet_of_subset_deductive
    (U : Set α) (hU : sys.IsFinitelyConsistent U) (Y : Finset α)
    (hY : (Y : Set α) ⊆ {a | ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u a}) :
    ∃ w : Finset α, (w : Set α) ⊆ U ∧ sys.EntSet w Y := by
  induction Y using Finset.induction_on with
  | empty =>
    exact ⟨∅, fun _ ha => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 ha)),
      fun _ ha => False.elim (Finset.notMem_empty _ ha)⟩
  | insert a s _ha ih =>
    have ha' : ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u a :=
      hY (Finset.mem_coe.2 (Finset.mem_insert_self a s))
    have hs' : (s : Set α) ⊆ {b | ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u b} := by
      intro b hb
      exact hY (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hb)))
    obtain ⟨ua, hua, hEnta⟩ := ha'
    obtain ⟨us, hus, hEnts⟩ := ih hs'
    refine ⟨ua ∪' us, ?_, ?_⟩
    · intro z hz
      rcases mem_funion.mp (Finset.mem_coe.1 hz) with h | h
      · exact hua (Finset.mem_coe.2 h)
      · exact hus (Finset.mem_coe.2 h)
    · intro b hb
      have hwU : (ua ∪' us : Set α) ⊆ U := by
        intro z hz
        rcases mem_funion.mp (Finset.mem_coe.1 hz) with h | h
        · exact hua (Finset.mem_coe.2 h)
        · exact hus (Finset.mem_coe.2 h)
      have hw : ua ∪' us ∈ sys.Con := hU _ hwU
      rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact sys.ent_trans hw (hU ua hua)
          (fun y hy => sys.ent_refl hw (mem_funion.mpr (Or.inl hy))) hEnta
      · exact sys.ent_trans hw (hU us hus)
          (fun y hy => sys.ent_refl hw (mem_funion.mpr (Or.inr hy))) (hEnts b hb')

/-- Deductive closure of a finitely consistent set. -/
def deductiveClosure (U : Set α) (hU : sys.IsFinitelyConsistent U) : sys.Element where
  carrier := {a | ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u a}
  consistent := by
    intro Y hY
    obtain ⟨w, hwU, hEnt⟩ := sys.exists_entSet_of_subset_deductive U hU Y hY
    have hw : w ∈ sys.Con := hU w hwU
    exact sys.con_subset (proposition_2_3_ii sys hw hEnt) (subset_funion_right _ _)
  closed := by
    intro Y a hY hEnt
    obtain ⟨w, hwU, hEntY⟩ := sys.exists_entSet_of_subset_deductive U hU Y hY
    have hw : w ∈ sys.Con := hU w hwU
    have hYcon : Y ∈ sys.Con :=
      sys.con_subset (proposition_2_3_ii sys hw hEntY) (subset_funion_right _ _)
    exact ⟨w, hwU, sys.ent_trans hw hYcon hEntY hEnt⟩

/-- Carrier union of a family of elements. -/
def familyUnionCarrier (S : Set sys.Element) : Set α :=
  {a | ∃ x ∈ S, a ∈ x.carrier}

/-- Join of a family whose carrier-union is finitely consistent. -/
def familySup (S : Set sys.Element)
    (hU : sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) : sys.Element :=
  sys.deductiveClosure (sys.familyUnionCarrier S) hU

/-- Binary join via deductive closure of `x.carrier ∪ y.carrier`, when consistent. -/
def join (x y : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) : sys.Element :=
  sys.deductiveClosure (x.carrier ∪ y.carrier) h
end InfoSys
end DomainTheory.InformationSystems
