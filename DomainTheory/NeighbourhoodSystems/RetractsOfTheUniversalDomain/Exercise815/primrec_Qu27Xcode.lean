/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem75
public import DomainTheory.Neighborhood.Definition610
public import DomainTheory.Neighborhood.Proposition611
public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.Exercise714
public import DomainTheory.Neighborhood.UComputablePresentation
public import DomainTheory.Neighborhood.Exercise815.Basic
public import DomainTheory.Neighborhood.Exercise815.primrec_QstepFn

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}













section UniversalSubsystem






theorem primrec_Q'Xcode {r : ℕ → ℕ} (hr : Nat.Primrec r) : Nat.Primrec (Q'Xcode r) :=
  primrec_foldCode (primrec_QstepFn hr) (Nat.Primrec.const 0)
    (Nat.Primrec.const UComputablePresentation.masterIdx) Nat.Primrec.id

end UniversalSubsystem
end DomainTheory.Neighborhood
