/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}





/-- **Bounded `∃` over a coded list preserves recursive enumerability.** If `R` is r.e. then so is
`fun d a => ∃ b ∈ decodeList d, R a b`: project out `b` (`REPred.proj`) over the conjunction of the
*recursively decidable* membership `b ∈ decodeList d` with the r.e. body `R a b`. -/
theorem bExists_decodeList_re {R : ℕ → ℕ → Prop} (hR : REPred₂ R) :
    REPred₂ (fun d a => ∃ b ∈ decodeList d, R a b) := by
  have hmem : RecDecidable₂ (fun d b => b ∈ decodeList d) := by
    have heq : RecDecidable₂ (fun e b => e = b) :=
      RecDecidable.natEq Nat.Primrec.left Nat.Primrec.right
    have hbase : RecDecidable₂ (fun d b => ∃ e ∈ decodeList d, e = b) := heq.bExistsList
    refine RecDecidable.of_iff (fun t => ?_) hbase
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨e, he, rfl⟩; exact he
  have hpart1 : REPred (fun w : ℕ => w.unpair.1 ∈ decodeList w.unpair.2.unpair.1) := by
    have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1) :=
      (Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left
    refine RecDecidable.re (RecDecidable.of_iff (fun w => ?_) (hmem.comp hg))
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hpart2 : REPred (fun w : ℕ => R w.unpair.2.unpair.2 w.unpair.1) := by
    have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.2 w.unpair.1) :=
      (Nat.Primrec.right.comp Nat.Primrec.right).pair Nat.Primrec.left
    refine REPred.of_iff (fun w => ?_) (REPred.comp hR hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun s => ?_) (hpart1.and hpart2).proj
  simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
