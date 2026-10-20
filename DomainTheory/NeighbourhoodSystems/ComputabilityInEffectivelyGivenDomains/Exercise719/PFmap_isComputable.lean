/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition710
public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise719.Basic
public import DomainTheory.Neighborhood.Exercise719.PFmap_isComputable_Ypd

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}





/-- **Exercise 7.19 (Scott's first question), packaged.** `ℙf` is a computable map between the
canonical effective presentations `ℙ𝒟`, `ℙℰ` (Proposition 7.10) whenever `f` is computable. -/
theorem PFmap_isComputable (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (consV : ℕ → ℕ) (hconsVp : Nat.Primrec consV)
    (hconsVs : ∀ a b, consV (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b)
    (consW : ℕ → ℕ) (hconsWp : Nat.Primrec consW)
    (hconsWs : ∀ a b, consW (Nat.pair a b) = 1 ↔ ∃ k, Q.X k ⊆ Q.X a ∩ Q.X b)
    {f : ApproximableMap V W} (hf : IsComputableMap P Q f) :
    IsComputableMap (V.PDPresentation P consV hconsVp hconsVs)
      (W.PDPresentation Q consW hconsWp hconsWs) (PFmap f) := by
  exact PFmap_isComputable_Ypd P Q hf

end DomainTheory.Neighborhood
