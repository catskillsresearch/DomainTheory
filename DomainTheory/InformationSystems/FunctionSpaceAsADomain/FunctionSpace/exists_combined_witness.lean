/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion_insert
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunCon
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.entSet_inputUnion_of_ent
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion_con_of_ent

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Combine entailment witnesses along a finite set of tokens (for `ent_trans`). -/
theorem exists_combined_witness {u' : Finset α} {s : Finset (FunToken A B)}
    {v : Finset (FunToken A B)}
    (hv : FunCon A B v) (hu' : u' ∈ A.Con)
    (hEntIn : ∀ q ∈ s, A.EntSet u' q.val.1)
    (hWit : ∀ q ∈ s, ∃ s_q ⊆ v, (∀ r ∈ s_q, A.EntSet q.val.1 r.val.1) ∧
      B.EntSet (funOutputUnion A B s_q) q.val.2) :
    ∃ S ⊆ v, (∀ r ∈ S, A.EntSet u' r.val.1) ∧
      B.EntSet (funOutputUnion A B S) (funOutputUnion A B s) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · intro _ hq
      exact False.elim (Finset.notMem_empty _ hq)
    · intro y hy
      exact False.elim (Finset.notMem_empty y hy)
  | insert q s' hqnot ih =>
    have hEntIn' : ∀ r ∈ s', A.EntSet u' r.val.1 := fun r hr =>
      hEntIn r (Finset.mem_insert_of_mem hr)
    have hWit' : ∀ r ∈ s', ∃ s_r ⊆ v, (∀ t ∈ s_r, A.EntSet r.val.1 t.val.1) ∧
        B.EntSet (funOutputUnion A B s_r) r.val.2 := fun r hr =>
      hWit r (Finset.mem_insert_of_mem hr)
    obtain ⟨S', hS'sub, hS'in, hS'out⟩ := ih hEntIn' hWit'
    obtain ⟨Sq, hSqsub, hSqin, hSqout⟩ := hWit q (Finset.mem_insert_self q s')
    refine ⟨S' ∪' Sq, funion_subset_iff.mpr ⟨hS'sub, hSqsub⟩, ?_, ?_⟩
    · intro r hr
      rcases mem_funion.mp hr with hr | hr
      · exact hS'in r hr
      · have hEnt_q : A.EntSet u' q.val.1 := hEntIn q (Finset.mem_insert_self q s')
        have hEnt_r : A.EntSet q.val.1 r.val.1 := hSqin r hr
        exact proposition_2_3_iv A hu' q.property.1 hEnt_q hEnt_r
    · rw [funOutputUnion_funion, funOutputUnion_insert]
      have hinS' : funInputUnion A B S' ∈ A.Con :=
        funInputUnion_con_of_ent A B hu' hS'in
      have houtS' : funOutputUnion A B S' ∈ B.Con := hv S' hS'sub hinS'
      have hinSq : funInputUnion A B Sq ∈ A.Con :=
        funInputUnion_con_of_ent A B q.property.1 hSqin
      have houtSq : funOutputUnion A B Sq ∈ B.Con := hv Sq hSqsub hinSq
      have hinUnion : funInputUnion A B (S' ∪' Sq) ∈ A.Con := by
        rw [funInputUnion_funion]
        have hEnt : A.EntSet u' (funInputUnion A B S' ∪' funInputUnion A B Sq) :=
          proposition_2_3_vi A
            (entSet_inputUnion_of_ent A B hS'in)
            (proposition_2_3_iv A hu' q.property.1
              (hEntIn q (Finset.mem_insert_self q s'))
              (entSet_inputUnion_of_ent A B hSqin))
        exact A.con_subset (proposition_2_3_ii A hu' hEnt) (subset_funion_right _ _)
      have houtUnion : funOutputUnion A B S' ∪' funOutputUnion A B Sq ∈ B.Con := by
        have : funOutputUnion A B (S' ∪' Sq) ∈ B.Con := hv _ (funion_subset_iff.mpr ⟨hS'sub, hSqsub⟩) hinUnion
        rwa [funOutputUnion_funion] at this
      have hEnt1 : B.EntSet (funOutputUnion A B S' ∪' funOutputUnion A B Sq)
          (funOutputUnion A B s') :=
        proposition_2_3_v B houtS' houtUnion (subset_funion_left _ _) hS'out
          (Finset.Subset.refl _)
      have hEnt2 : B.EntSet (funOutputUnion A B S' ∪' funOutputUnion A B Sq) q.val.2 :=
        proposition_2_3_v B houtSq houtUnion (subset_funion_right _ _) hSqout
          (Finset.Subset.refl _)
      exact proposition_2_3_vi B hEnt2 hEnt1

end InfoSys

end DomainTheory.InformationSystems
