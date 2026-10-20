/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88h.Basic
public import DomainTheory.Neighborhood.Theorem88h.diagFixed_iff_fixedNbhd_mem
public import DomainTheory.Neighborhood.Theorem88h.diagFixed_isREPred
public import DomainTheory.Neighborhood.Theorem88h.diagFixed_exists_qChar
public import DomainTheory.Neighborhood.Theorem88i.Basic
public import DomainTheory.Neighborhood.Theorem88i.myStep_diagFixed_of_diagFixed

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)





variable {P qChar cons}

/-- **The fold invariant, over an arbitrary starting accumulator.** -/
theorem myFold_diagFixed_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    ∀ {r : ℕ}, DiagFixed P a r → DiagFixed P a (l.foldl (myStep P qChar cons) r) := by
  induction l with
  | nil => intro r hr; simpa using hr
  | cons e rest ih =>
    intro r hr
    rw [List.foldl_cons]
    exact ih (myStep_diagFixed_of_diagFixed hqChar hcons hr e)

end DomainTheory.Neighborhood
