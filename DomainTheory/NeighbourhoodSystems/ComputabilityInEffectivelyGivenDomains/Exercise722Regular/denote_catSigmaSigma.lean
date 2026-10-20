/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722


















/-- **`denote` is far from injective: `Σ · Σ = Σ`.** A nontrivial language identity (with distinct
syntax), so relation (i) `Xₙ∩Xₘ = X_k` is *not* syntactic equality of codes — it is genuine
regular-language equivalence, the whole difficulty of the exercise. -/
theorem denote_catSigmaSigma : denote (.cat .sigma .sigma) = denote .sigma := by
  ext w
  simp only [denote_cat, denote_sigma, mem_concat, Set.mem_univ, iff_true]
  exact ⟨[], trivial, w, trivial, rfl⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
