/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_zero
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_succ
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_ofNat_succ
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStep_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































/-- **Scott 1976, (2.27).** The fixed point of the primrec step agrees
with integer recursion. -/
theorem primRecVal_fix (a f : Pomega) : ∀ n,
    funOf (fix (primRecStep a f)) (ofNat n) = primRecVal a f n
  | 0 => by
    have hfix := (theorem_1_4 (primRecStep_isScottContinuous a f)).1
    calc funOf (fix (primRecStep a f)) (ofNat 0)
        = funOf (primRecStep a f (fix (primRecStep a f))) (ofNat 0) := by
          rw [hfix]
      _ = condSet (ofNat 0) a
            (funOf (funOf f (predSet (ofNat 0)))
              (funOf (fix (primRecStep a f)) (predSet (ofNat 0)))) :=
          primRecStep_app a f _ _
      _ = a := eq_2_7_zero _ _
  | n + 1 => by
    have hfix := (theorem_1_4 (primRecStep_isScottContinuous a f)).1
    calc funOf (fix (primRecStep a f)) (ofNat (n + 1))
        = funOf (primRecStep a f (fix (primRecStep a f))) (ofNat (n + 1)) := by
          rw [hfix]
      _ = condSet (ofNat (n + 1)) a
            (funOf (funOf f (predSet (ofNat (n + 1))))
              (funOf (fix (primRecStep a f)) (predSet (ofNat (n + 1))))) :=
          primRecStep_app a f _ _
      _ = funOf (funOf f (ofNat n))
            (funOf (fix (primRecStep a f)) (ofNat n)) := by
          rw [eq_2_7_succ, predSet_ofNat_succ]
      _ = funOf (funOf f (ofNat n)) (primRecVal a f n) := by
          rw [primRecVal_fix a f n]

end DomainTheory.DataTypesAsLattices
