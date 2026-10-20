/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import DomainTheory.Neighborhood.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.Neighborhood.Exercise722.Basic
public import DomainTheory.Neighborhood.Exercise722.concat_singleton

@[expose] public section


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap

























/-- **Exercise 7.22 (homomorphism part): `emb` is a semigroup homomorphism**,
`emb (σ ++ τ) = emb σ · emb τ`. Forward: from `σ ++ τ ∈ Z`, the witnesses `X = {σ}`, `Y = {τ}` give
`{σ}{τ} = {σ ++ τ} ⊆ Z`. Converse: if `{σ}` ∈ `emb σ`, `{τ}` ∈ `emb τ` with `XY ⊆ Z` then
`σ ++ τ ∈ XY ⊆ Z`. -/
theorem emb_mul (σ τ : List Bool) : emb (σ ++ τ) = mulElem (emb σ) (emb τ) := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  constructor
  · rintro ⟨hZ, hστ⟩
    refine ⟨hZ, {σ}, ⟨InS.singleton σ, rfl⟩, {τ}, ⟨InS.singleton τ, rfl⟩, ?_⟩
    rw [concat_singleton]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw; exact hστ
  · rintro ⟨hZ, X, ⟨_, hσX⟩, Y, ⟨_, hτY⟩, hsub⟩
    exact ⟨hZ, hsub (append_mem_concat hσX hτY)⟩

end Exercise722
end DomainTheory.Neighborhood
