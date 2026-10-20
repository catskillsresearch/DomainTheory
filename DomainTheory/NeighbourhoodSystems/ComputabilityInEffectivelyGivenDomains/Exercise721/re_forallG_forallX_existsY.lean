/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise719
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise721.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}







/-- **Three nested bounded quantifiers preserve recursive enumerability.** If `R` is r.e. (in the
paired form `R g x y`) then so is `∀ g ∈ dl w.1, ∀ x ∈ dl w.2.1, ∃ y ∈ dl w.2.2, R g x y`. Built from
the bounded-`∃` lemma `bExists_decodeList_re` (Exercise 7.19) and the parameterised bounded-`∀` lemma
`REPred.forall_mem_decodeList₂`, layered with primitive-recursive re-indexings. -/
theorem re_forallG_forallX_existsY {R : ℕ → ℕ → ℕ → Prop}
    (hR : REPred (fun s => R s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2)) :
    REPred (fun w => ∀ g ∈ decodeList w.unpair.1, ∀ x ∈ decodeList w.unpair.2.unpair.1,
      ∃ y ∈ decodeList w.unpair.2.unpair.2, R g x y) := by
  -- reindex `⟨g,x,y⟩ = ⟨s.1.1, s.1.2, s.2⟩` ↦ `⟨g,⟨x,y⟩⟩`
  have hm1 : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.1.unpair.1
      (Nat.pair s.unpair.1.unpair.2 s.unpair.2)) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair
      ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)
  have hR2 : REPred₂ (fun gx y => R gx.unpair.1 gx.unpair.2 y) := by
    show REPred (fun t => R t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2)
    refine REPred.of_iff (fun s => ?_) (hR.comp hm1)
    simp only [unpair_pair_fst, unpair_pair_snd]
  -- bounded `∃ y`
  have hE : REPred (fun u => ∃ b ∈ decodeList u.unpair.1,
      R u.unpair.2.unpair.1 u.unpair.2.unpair.2 b) := bExists_decodeList_re hR2
  -- bounded `∀ x` (parameters `⟨Bc, g⟩`)
  have hm2 : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1.unpair.1
      (Nat.pair t.unpair.1.unpair.2 t.unpair.2)) := hm1
  have hF : REPred₂ (fun param x => ∃ y ∈ decodeList param.unpair.1,
      R param.unpair.2 x y) := by
    show REPred (fun t => ∃ y ∈ decodeList t.unpair.1.unpair.1,
      R t.unpair.1.unpair.2 t.unpair.2 y)
    refine REPred.of_iff (fun t => ?_) (hE.comp hm2)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hFfull : REPred (fun t => ∀ x ∈ decodeList t.unpair.2,
      ∃ y ∈ decodeList t.unpair.1.unpair.1, R t.unpair.1.unpair.2 x y) :=
    REPred.forall_mem_decodeList₂ hF
  -- bounded `∀ g` (parameters `⟨Bc, Ac⟩`)
  have hm3 : Nat.Primrec (fun t : ℕ => Nat.pair
      (Nat.pair t.unpair.1.unpair.1 t.unpair.2) t.unpair.1.unpair.2) :=
    ((Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right).pair
      (Nat.Primrec.right.comp Nat.Primrec.left)
  have hG : REPred₂ (fun param g => ∀ x ∈ decodeList param.unpair.2,
      ∃ y ∈ decodeList param.unpair.1, R g x y) := by
    show REPred (fun t => ∀ x ∈ decodeList t.unpair.1.unpair.2,
      ∃ y ∈ decodeList t.unpair.1.unpair.1, R t.unpair.2 x y)
    refine REPred.of_iff (fun t => ?_) (hFfull.comp hm3)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hGfull : REPred (fun t => ∀ g ∈ decodeList t.unpair.2,
      ∀ x ∈ decodeList t.unpair.1.unpair.2,
        ∃ y ∈ decodeList t.unpair.1.unpair.1, R g x y) :=
    REPred.forall_mem_decodeList₂ hG
  -- final reindex to `w = ⟨Φc, ⟨Ac, Bc⟩⟩`
  have hm4 : Nat.Primrec (fun w : ℕ => Nat.pair
      (Nat.pair w.unpair.2.unpair.2 w.unpair.2.unpair.1) w.unpair.1) :=
    ((Nat.Primrec.right.comp Nat.Primrec.right).pair
      (Nat.Primrec.left.comp Nat.Primrec.right)).pair Nat.Primrec.left
  refine REPred.of_iff (fun w => ?_) (hGfull.comp hm4)
  simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.Neighborhood
