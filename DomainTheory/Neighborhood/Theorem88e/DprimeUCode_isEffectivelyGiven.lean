/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88d.Basic
public import DomainTheory.Neighborhood.Theorem88d.mem_decodeQPairList_appendCode
public import DomainTheory.Neighborhood.Theorem88d.presentedIntervals_decodeQPairList_appendCode
public import DomainTheory.Neighborhood.Theorem88d.primrec_unionUX
public import DomainTheory.Neighborhood.Theorem88d.U_mem_union_UX
public import DomainTheory.Neighborhood.Theorem88d.UX_unionUX
public import DomainTheory.Neighborhood.Theorem88d.primrec_wY
public import DomainTheory.Neighborhood.Theorem88d.primrec_wState
public import DomainTheory.Neighborhood.Theorem88d.primrec_stateRem
public import DomainTheory.Neighborhood.Theorem88d.primrec_statePos
public import DomainTheory.Neighborhood.Theorem88d.primrec_stateNeg
public import DomainTheory.Neighborhood.Theorem88d.primrec_stateCode
public import DomainTheory.Neighborhood.Theorem88d.primrec_atomBase
public import DomainTheory.Neighborhood.Theorem88d.primrec_atomStep
public import DomainTheory.Neighborhood.Theorem88d.primrec_datomDec
public import DomainTheory.Neighborhood.Theorem88d.datomDec_eq_zero
public import DomainTheory.Neighborhood.Theorem88d.primrec_atomUCodeState
public import DomainTheory.Neighborhood.Theorem88d.primrec_atomUPos
public import DomainTheory.Neighborhood.Theorem88d.primrec_atomUNeg
public import DomainTheory.Neighborhood.Theorem88d.primrec_atomUCode
public import DomainTheory.Neighborhood.Theorem88d.atomUEmpty_congr
public import DomainTheory.Neighborhood.Theorem88d.atomUCode_mem
public import DomainTheory.Neighborhood.Theorem88d.deltaOf_mod_two_pow_of_lt
public import DomainTheory.Neighborhood.Theorem88d.primrec_atomUEmpty
public import DomainTheory.Neighborhood.Theorem88d.primrec_yFoldStep
public import DomainTheory.Neighborhood.Theorem88d.yFold_zero
public import DomainTheory.Neighborhood.Theorem88d.yFold_succ
public import DomainTheory.Neighborhood.Theorem88d.primrec_yFold
public import DomainTheory.Neighborhood.Theorem88d.atomUEmpty_zero_or_one
public import DomainTheory.Neighborhood.Theorem88d.yFoldStep_eq
public import DomainTheory.Neighborhood.Theorem88d.yFold_found_le_one
public import DomainTheory.Neighborhood.Theorem88d.yFold_found_iff
public import DomainTheory.Neighborhood.Theorem88d.yFold_mem_iff
public import DomainTheory.Neighborhood.Theorem88d.yFold_two_pow_found
public import DomainTheory.Neighborhood.Theorem88d.primrec_YseqCode
public import DomainTheory.Neighborhood.Theorem88d.mem_UX_YseqCode_iff
public import DomainTheory.Neighborhood.Theorem88d.atomUCode_succ_true
public import DomainTheory.Neighborhood.Theorem88d.eq_of_deltaOf_agree_of_lt_two_pow
public import DomainTheory.Neighborhood.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.Neighborhood.Theorem88d.atomUCodeState_congr_twin
public import DomainTheory.Neighborhood.Theorem88d.atomUCode_succ_false
public import DomainTheory.Neighborhood.Theorem88d.DAtom_union
public import DomainTheory.Neighborhood.Theorem88d.atomUCode_eq_genAtomYseqCode
public import DomainTheory.Neighborhood.Theorem88d.atomUCode_inter_succ_empty_of_junk
public import DomainTheory.Neighborhood.Theorem88d.genAtom_Yc_empty_iff
public import DomainTheory.Neighborhood.Theorem88c.Basic
public import DomainTheory.Neighborhood.Theorem88c.DprimeU_isEffectivelyGiven
public import DomainTheory.Neighborhood.Theorem88e.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)




































/-- **Theorem 8.8(b)(vii)(3), full statement.** `D''` is effectively given, `D ≅ᴰ D''`, and
`D'' ◁ U`. -/
theorem DprimeUCode_isEffectivelyGiven : (DprimeUCode P).IsEffectivelyGiven :=
  ⟨DprimeUCodePresentation P⟩

end DomainTheory.Neighborhood
