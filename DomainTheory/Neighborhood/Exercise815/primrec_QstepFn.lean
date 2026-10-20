/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Definition610
import DomainTheory.Neighborhood.Proposition611
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Exercise714
import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.Exercise815.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}













section UniversalSubsystem





theorem primrec_QstepFn {r : ℕ → ℕ} (hr : Nat.Primrec r) : Nat.Primrec (QstepFn r) := by
  unfold QstepFn
  have h1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have h2 : Nat.Primrec (fun t : ℕ => r t.unpair.1) := hr.comp Nat.Primrec.left
  exact (Uinter_primrec.comp (h1.pair h2)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd]

end UniversalSubsystem
end DomainTheory.Neighborhood
