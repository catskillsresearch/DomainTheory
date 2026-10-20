/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Computability.Partrec
import Mathlib.Tactic.Ring
import DomainTheory.Neighborhood.Exercise722Regular
import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv
import DomainTheory.Neighborhood.Recursive.Basic


namespace Domain.Recursive













































































































































































set_option maxHeartbeats 1000000 in
/-- `fuelTable bodyLookup · ·` is primitive recursive in `(bound, fuel)` (coded `pair bound
fuel`), whenever `bodyLookup` is. Mirrors `primrec_tabCode`'s `Nat.Primrec.prec` packaging. -/
theorem primrec_fuelTable {bodyLookup : ℕ → ℕ} (hbodyLookup : Nat.Primrec bodyLookup) :
    Nat.Primrec (fun t => fuelTable bodyLookup t.unpair.1 t.unpair.2) := by
  have hgLookup : Nat.Primrec (fun v => bodyLookup (Nat.pair v.unpair.2 v.unpair.1)) :=
    hbodyLookup.comp (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)
  have htab := primrec_tabCode hgLookup
  have hf : Nat.Primrec (fun bound => tabCode (fun _ => 0) (Nat.pair (bound + 1) 0) (bound + 1)) :=
    ((primrec_tabCode (Nat.Primrec.const 0)).comp
      (Nat.Primrec.pair
        (Nat.Primrec.pair (primrec_add₂ Nat.Primrec.id (Nat.Primrec.const 1)) (Nat.Primrec.const 0))
        (primrec_add₂ Nat.Primrec.id (Nat.Primrec.const 1)))).of_eq fun bound => by simp
  have hpack : Nat.Primrec (fun w =>
      Nat.pair (Nat.pair (w.unpair.1 + 1) w.unpair.2.unpair.2) (w.unpair.1 + 1)) :=
    Nat.Primrec.pair
      (Nat.Primrec.pair (primrec_add₂ Nat.Primrec.left (Nat.Primrec.const 1))
        (Nat.Primrec.right.comp Nat.Primrec.right))
      (primrec_add₂ Nat.Primrec.left (Nat.Primrec.const 1))
  have hg : Nat.Primrec (fun w => fuelTableStep bodyLookup w.unpair.1 w.unpair.2.unpair.2) :=
    (htab.comp hpack).of_eq fun w => by simp [fuelTableStep]
  have haux : ∀ bound fuel, Nat.rec (motive := fun _ => ℕ)
      (tabCode (fun _ => 0) (Nat.pair (bound + 1) 0) (bound + 1))
      (fun _ IH => fuelTableStep bodyLookup bound IH) fuel = fuelTable bodyLookup bound fuel := by
    intro bound fuel
    induction fuel with
    | zero => rfl
    | succ fuel ih => show fuelTableStep bodyLookup bound _ = fuelTableStep bodyLookup bound _; rw [ih]
  refine (Nat.Primrec.prec hf hg).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  exact haux t.unpair.1 t.unpair.2

end Domain.Recursive
