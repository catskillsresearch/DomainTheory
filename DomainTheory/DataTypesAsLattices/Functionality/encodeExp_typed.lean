/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.typed_pairSeq_tensorR
import DomainTheory.DataTypesAsLattices.Functionality.tensor4_app
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_zero
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_one
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_two
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_three
import DomainTheory.DataTypesAsLattices.Functionality.eq_4_44
import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl0
import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl1
import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl2
import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl3
import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl4
import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl5
import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl6
import DomainTheory.DataTypesAsLattices.Functionality.typed_ofNat_intR
import DomainTheory.DataTypesAsLattices.Functionality.typed_bot_botElem


namespace DomainTheory.DataTypesAsLattices

































theorem encodeExp_typed : ∀ τ : LambTerm, typed (encodeExp τ) expR := by
  intro τ
  induction τ with
  | var n =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl0 (typed_ofNat_intR n)
  | zero =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl1 typed_bot_botElem
  | succ τ ih =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl2 ih
  | pred τ ih =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl3 ih
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl4 ?_
    rw [typed, tensor4_app, seq4_app_zero, seq4_app_one, seq4_app_two,
      seq4_app_three, ← ihθ, ← ihτ, ← ihσ, ← ihρ]
  | app τ σ ihτ ihσ =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl5 ?_
    exact (typed_pairSeq_tensorR expR expR _ _).mpr ⟨ihτ, ihσ⟩
  | lam n τ ih =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl6 ?_
    exact (typed_pairSeq_tensorR intR expR _ _).mpr ⟨typed_ofNat_intR n, ih⟩

end DomainTheory.DataTypesAsLattices
