/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb_ofNat
public import DomainTheory.DataTypesAsLattices.Computability.pairComb_app
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC_realizes
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC_realizes
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpC_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4





































theorem precC_realizes {f g : Pomega} {p q : ℕ → ℕ}
    (hf : Realizes f p) (hg : Realizes g q) :
    Realizes (precC f g)
      (Nat.unpaired fun z n => n.rec (p z) fun y ih => q (Nat.pair z (Nat.pair y ih))) := by
  intro w
  rw [precC, precTerm, theorem_2_2_beta]
  simp only [interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (6 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (7 : ℕ) ≠ 0),
    precEnv]
  simp [Function.update]
  rw [unpairFstC_realizes, unpairSndC_realizes, hf, primRecOpC_app,
    primRecComb_ofNat]
  let z := w.unpair.1
  let step : Pomega :=
    interp (.lam 1 (.lam 2
      (.app (.var 5)
        (.app (.app (.var 8) (ofNat z |> fun _ => .app (.var 6) (.var 0)))
          (.app (.app (.var 8) (.var 1)) (.var 2))))))
      (Function.update (precEnv f g) 0 (ofNat w))
  have hstep (y ih : ℕ) :
      (step ⬝ ofNat y) ⬝ ofNat ih =
        ofNat (q (Nat.pair z (Nat.pair y ih))) := by
    dsimp [step, z]
    rw [theorem_2_2_beta, theorem_2_2_beta]
    simp [interp, envSet, Function.update, precEnv]
    rw [unpairFstC_realizes, pairComb_app, pairComb_app, hg]
  have hrec : ∀ n,
      primRecVal (ofNat (p z)) step n =
        ofNat (n.rec (p z) fun y ih => q (Nat.pair z (Nat.pair y ih))) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change (step ⬝ ofNat n) ⬝ primRecVal (ofNat (p z)) step n = _
      rw [ih, hstep]
  exact hrec w.unpair.2

end DomainTheory.DataTypesAsLattices
