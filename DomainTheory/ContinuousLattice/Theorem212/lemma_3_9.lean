/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.Constructions
import DomainTheory.ContinuousLattice.FunctionSpaces
import DomainTheory.ContinuousLattice.Theorem212.Basic


namespace DomainTheory.ContinuousLattice

open Topology Set



universe u




section Lemma39

variable {X Y D D' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompleteLattice D] [CompleteLattice D']

/-- **Scott 1972, Lemma 3.9.** With `e : X → Y` a subspace embedding and `i, j : D ⇄ D'` a
projection on the range, if continuous `f : X → D` and `g : X → D'` satisfy `f = j ∘ g`, then the
maximal extensions (Proposition 3.8) satisfy `f̄ = j ∘ ḡ`.

The proof is Scott's, recast through the faithful `scottExtend`:
* `j ∘ ḡ ⊑ f̄`: `j ∘ ḡ` is a continuous solution of `(j ∘ ḡ) ∘ e = j ∘ g = f`, so maximality of
  `f̄` (`scottExtend_maximal`) gives the bound;
* `i ∘ f̄ ⊑ ḡ`: `(i ∘ f̄) ∘ e = i ∘ f = i ∘ j ∘ g ⊑ g` (since `i ∘ j ⊑ id`), so the *sub*-solution
  maximality of `ḡ` (`scottExtend_maximal_le`, the remark after 3.8) gives the bound;
* combining: `f̄ = j ∘ i ∘ f̄ ⊑ j ∘ ḡ ⊑ f̄` (using `j ∘ i = id` and monotonicity of `j`). -/
theorem lemma_3_9 (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D')
    (P : IsContinuousLatticeProjection D D') (e : X → Y) (he : IsEmbedding e)
    {f : X → D} {g : X → D'} (hf : @Continuous X D _ scottTopologicalSpace f)
    (hg : @Continuous X D' _ scottTopologicalSpace g)
    (hfg : ∀ x, f x = (P.retr : D' → D) (g x)) (y : Y) :
    scottExtend e f y = (P.retr : D' → D) (scottExtend e g y) := by
  have hfbar : @Continuous Y D _ scottTopologicalSpace (scottExtend e f) :=
    scottExtend_continuous hD e f
  have hgbar : @Continuous Y D' _ scottTopologicalSpace (scottExtend e g) :=
    scottExtend_continuous hD' e g
  -- `j ∘ ḡ` and `i ∘ f̄` are continuous (Scott topology is not an instance; register it locally so
  -- `Continuous.comp` can fire, scoped to avoid the lattice `≤` clashing with specialization order).
  have hjg : @Continuous Y D _ scottTopologicalSpace (fun z => (P.retr : D' → D) (scottExtend e g z)) := by
    let : TopologicalSpace D := scottTopologicalSpace
    let : TopologicalSpace D' := scottTopologicalSpace
    exact P.retr.continuous.comp hgbar
  have hif : @Continuous Y D' _ scottTopologicalSpace (fun z => (P.incl : D → D') (scottExtend e f z)) := by
    let : TopologicalSpace D := scottTopologicalSpace
    let : TopologicalSpace D' := scottTopologicalSpace
    exact P.incl.continuous.comp hfbar
  -- Step A: `j ∘ ḡ ⊑ f̄`.
  have hA : ∀ z, (P.retr : D' → D) (scottExtend e g z) ≤ scottExtend e f z := by
    intro z
    refine scottExtend_maximal hD e hjg ?_ z
    intro x
    show (P.retr : D' → D) (scottExtend e g (e x)) = f x
    rw [scottExtend_eq_of_continuous hD' e he g hg x, ← hfg x]
  -- Step B: `i ∘ f̄ ⊑ ḡ`.
  have hB : ∀ z, (P.incl : D → D') (scottExtend e f z) ≤ scottExtend e g z := by
    intro z
    refine scottExtend_maximal_le hD' e hif ?_ z
    intro x
    show (P.incl : D → D') (scottExtend e f (e x)) ≤ g x
    rw [scottExtend_eq_of_continuous hD e he f hf x, hfg x]
    exact P.incl_retr_le (g x)
  refine le_antisymm ?_ (hA y)
  calc scottExtend e f y
      = (P.retr : D' → D) ((P.incl : D → D') (scottExtend e f y)) :=
        (P.retr_incl (scottExtend e f y)).symm
    _ ≤ (P.retr : D' → D) (scottExtend e g y) := P.retr.monotone (hB y)

end Lemma39
end DomainTheory.ContinuousLattice
