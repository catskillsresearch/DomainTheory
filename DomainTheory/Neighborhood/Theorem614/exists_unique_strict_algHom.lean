/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition613
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem614.Basic
import DomainTheory.Neighborhood.Theorem614.nonempty_strict_algHom
import DomainTheory.Neighborhood.Theorem614.algHom_unique


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

universe w

namespace Theorem614


variable {α : Type w}
















































/-- **Theorem 6.14 (Scott 1981, PRG-19) — initial `T`-algebra.** When `{Γ}` is the one-point
generating system, the canonical solution `𝒟 = ⋃ₙ Tⁿ({Γ})` is the **initial** `T`-algebra among the
strict algebras: for every `T`-algebra `B` with a strict structure map there is a *unique* strict
homomorphism `𝒟 → B`. (Existence is Theorem 6.9; uniqueness is the `ρₙ` projection-chain argument.) -/
theorem exists_unique_strict_algHom (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (hk : IsStrict B.str) :
    ∃ g : AlgHom (colimAlg s) B, IsStrict g.hom ∧
      ∀ g' : AlgHom (colimAlg s) B, IsStrict g'.hom → g' = g := by
  obtain ⟨⟨g, hg⟩⟩ := nonempty_strict_algHom s B hk
  exact ⟨g, hg, fun g' hg' => algHom_unique s hΓ B g' g hg' hg⟩

end Theorem614
end DomainTheory.Neighborhood
