/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_zero
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_one
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_two
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_three
import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion_ofNat
import DomainTheory.DataTypesAsLattices.Functionality.Hfun_app2
import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag0
import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag1
import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag2
import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag3
import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag4
import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag5
import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag6


namespace DomainTheory.DataTypesAsLattices
















































theorem Hfun_interp : ∀ τ : LambTerm, ∀ t : Pomega,
    funOf (funOf Hfun (encodeExp τ)) t = Hinterp τ t := by
  intro τ
  induction τ with
  | var n =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag0]
    rfl
  | zero =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag1]
    rfl
  | succ τ ih =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag2]
    simp only [hSucc, hApply, expPayload, tagInj_one]
    rw [ih]
    rfl
  | pred τ ih =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag3]
    simp only [hPred, hApply, expPayload, tagInj_one]
    rw [ih]
    rfl
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag4]
    simp only [hCond, hApply, expPayload, tagInj_one, seq4_app_zero,
      seq4_app_one, seq4_app_two, seq4_app_three]
    rw [ihθ, ihτ, ihσ, ihρ]
    rfl
  | app τ σ ihτ ihσ =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag5]
    simp only [hApp, hApply, expPayload, tagInj_one, pairSeq_app_zero,
      pairSeq_app_one]
    rw [ihτ, ihσ]
    rfl
  | lam n τ ih =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep_tag6]
    simp only [hLam, hApply, expPayload, tagInj_one, pairSeq_app_zero,
      pairSeq_app_one, updateEnvUnion_ofNat]
    congr 1
    apply congrArg graph
    funext x
    exact ih _

end DomainTheory.DataTypesAsLattices
