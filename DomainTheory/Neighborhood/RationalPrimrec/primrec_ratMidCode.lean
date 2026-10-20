/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Recursive
import DomainTheory.Neighborhood.RationalPrimrec.Basic
import DomainTheory.Neighborhood.RationalPrimrec.primrec_qNumP
import DomainTheory.Neighborhood.RationalPrimrec.primrec_qNumN
import DomainTheory.Neighborhood.RationalPrimrec.primrec_qDen


namespace DomainTheory.Neighborhood

open Domain.Recursive

























theorem primrec_ratMidCode : Nat.Primrec ratMidCode := by
  have hc1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hc2 : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hnumP : Nat.Primrec (fun t : ℕ =>
      qNumP t.unpair.1 * qDen t.unpair.2 + qNumP t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumP.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumP.comp hc2) (primrec_qDen.comp hc1))
  have hnumN : Nat.Primrec (fun t : ℕ =>
      qNumN t.unpair.1 * qDen t.unpair.2 + qNumN t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumN.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumN.comp hc2) (primrec_qDen.comp hc1))
  have hden : Nat.Primrec (fun t : ℕ => 2 * qDen t.unpair.1 * qDen t.unpair.2 - 1) :=
    primrec_sub₂
      (primrec_mul₂ (primrec_mul₂ (Nat.Primrec.const 2) (primrec_qDen.comp hc1))
        (primrec_qDen.comp hc2))
      (Nat.Primrec.const 1)
  exact (Nat.Primrec.pair (Nat.Primrec.pair hnumP hnumN) hden).of_eq fun t => by
    simp only [ratMidCode]

end DomainTheory.Neighborhood
