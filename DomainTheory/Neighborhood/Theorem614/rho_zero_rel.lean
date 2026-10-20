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


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

universe w

namespace Theorem614


variable {α : Type w}















































/-- **`ρ₀ = ⊥`** when `{Γ}` is the trivial one-point system: `ρ₀` relates `X` only to the master.
This is where Scott's `{Γ}` (a *one-point* domain) is used. -/
theorem rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    {X Y : Set s.Tok} :
    (rho s 0).rel X Y ↔ (colim s).mem X ∧ Y = (colim s).master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcX, hcY, z, hz, _, hzY⟩
    have hzm : z = s.Γ.master := hΓ z hz
    subst hzm
    refine ⟨hcX, Set.Subset.antisymm ((colim s).sub_master hcY) ?_⟩
    rw [colim_master]; exact hzY
  · rintro ⟨hcX, rfl⟩
    refine ⟨hcX, (colim s).master_mem, s.Γ.master, s.Γ.master_mem, ?_, ?_⟩
    · have h := (colim s).sub_master hcX; rwa [colim_master] at h
    · rw [colim_master]

end Theorem614
end DomainTheory.Neighborhood
