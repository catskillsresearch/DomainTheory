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
import DomainTheory.Neighborhood.Exercise815.primrec_QstepFn


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}













section UniversalSubsystem






theorem primrec_Q'Xcode {r : ℕ → ℕ} (hr : Nat.Primrec r) : Nat.Primrec (Q'Xcode r) :=
  primrec_foldCode (primrec_QstepFn hr) (Nat.Primrec.const 0)
    (Nat.Primrec.const UComputablePresentation.masterIdx) Nat.Primrec.id

end UniversalSubsystem
end DomainTheory.Neighborhood
