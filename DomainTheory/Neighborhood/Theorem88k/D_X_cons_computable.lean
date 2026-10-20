/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88j.Basic
public import DomainTheory.Neighborhood.Theorem88j.D_X_mem
public import DomainTheory.Neighborhood.Theorem88j.D_X_of_diagFixed
public import DomainTheory.Neighborhood.Theorem88j.D_X_surj
public import DomainTheory.Neighborhood.Theorem88k.Basic
public import DomainTheory.Neighborhood.Theorem88k.D_X_cons_iff

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}

variable (P qChar cons)

/-- **Theorem 8.8(c), Part 4 of 6, second half (`cons_computable`).** `D_X`-consistency is
`P.cons_computable` composed with the same primitive-recursive `myFoldCode`-pair reindex, via the
equivalence `D_X_cons_iff`. -/
theorem D_X_cons_computable {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    RecDecidable₂ (fun c₁ c₂ =>
      ∃ k, D_X P qChar cons k ⊆ D_X P qChar cons c₁ ∩ D_X P qChar cons c₂) := by
  have hmf : Nat.Primrec (myFoldCode P qChar cons) := primrec_myFoldCode P qChar cons hqCharp hconsp
  have hreindex : Nat.Primrec (fun t : ℕ =>
      Nat.pair (myFoldCode P qChar cons t.unpair.1) (myFoldCode P qChar cons t.unpair.2)) :=
    (hmf.comp Nat.Primrec.left).pair (hmf.comp Nat.Primrec.right)
  refine RecDecidable.of_iff (fun t => ?_) (P.cons_computable.comp hreindex)
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact D_X_cons_iff hqChar hcons t.unpair.1 t.unpair.2

end DomainTheory.Neighborhood
