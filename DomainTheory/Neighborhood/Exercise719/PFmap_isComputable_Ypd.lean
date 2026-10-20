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
public import DomainTheory.Neighborhood.Exercise719.bExists_decodeList_re
public import DomainTheory.Neighborhood.Exercise719.PFmap_rel_Ypd_iff

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}





/-- **Exercise 7.19 (Scott's first question) — `ℙf` is computable when `f` is.** Stated at the level
of the `ℙ𝒟`-codes of Proposition 7.10 (`Y_c = ⋃_{a∈dl c} ↓Xₐ`): the relation `(ℙf).rel (Y_c) (Y_d)`
is recursively enumerable in `(c, d)`. -/
theorem PFmap_isComputable_Ypd (P : ComputablePresentation V) (Q : ComputablePresentation W)
    {f : ApproximableMap V W} (hf : IsComputableMap P Q f) :
    REPred₂ (fun c d => (PFmap f).rel (V.Ypd P c) (W.Ypd Q d)) := by
  have hR : REPred₂ (fun a b => f.rel (P.X a) (Q.X b)) := hf
  have hInner : REPred₂ (fun d a => ∃ b ∈ decodeList d, f.rel (P.X a) (Q.X b)) :=
    bExists_decodeList_re hR
  have hForall := REPred.forall_mem_decodeList₂ hInner
  have hswap : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2 s.unpair.1) :=
    Nat.Primrec.right.pair Nat.Primrec.left
  refine REPred.of_iff (fun s => ?_) (hForall.comp hswap)
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact PFmap_rel_Ypd_iff P Q f

end DomainTheory.Neighborhood
