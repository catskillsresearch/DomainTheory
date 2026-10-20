/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88k.Basic
public import DomainTheory.Neighborhood.Theorem88k.D_X_cons_iff
public import DomainTheory.Neighborhood.Theorem88k.D_X_interEq_computable
public import DomainTheory.Neighborhood.Theorem88k.D_X_cons_computable
public import DomainTheory.Neighborhood.Theorem88l.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}




variable (P qChar cons)

theorem D_inter_primrec : Nat.Primrec (fun t => D_inter t.unpair.1 t.unpair.2) :=
  primrec_appendListCode

end DomainTheory.Neighborhood
