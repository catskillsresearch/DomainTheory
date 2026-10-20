/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.LevelSetPrimrec
public import DomainTheory.Neighborhood.MinLevel.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive



theorem primrec_isPeriodicMask :
    Nat.Primrec (fun t => isPeriodicMask t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hj : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hmodj : Nat.Primrec (fun t : ℕ => myModPow2 t.unpair.2.unpair.2 (2 ^ t.unpair.2.unpair.1)) :=
    (primrec_myModPow2.comp (hm.pair (primrec_two_pow hj))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hmodk : Nat.Primrec (fun t : ℕ => myModPow2 t.unpair.2.unpair.2 (2 ^ t.unpair.1)) :=
    (primrec_myModPow2.comp (hm.pair (primrec_two_pow hk))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hups : Nat.Primrec (fun t : ℕ =>
      myUpsample t.unpair.2.unpair.1 t.unpair.1 (myModPow2 t.unpair.2.unpair.2
        (2 ^ t.unpair.2.unpair.1))) :=
    (primrec_myUpsample.comp (hj.pair (hk.pair hmodj))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_isZero.comp (primrec_add₂ (primrec_sub₂ hups hmodk)
    (primrec_sub₂ hmodk hups))).of_eq fun t => rfl

end DomainTheory.Neighborhood
