/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise817
public import DomainTheory.Neighborhood.Proposition810b
public import DomainTheory.Neighborhood.Exercise326Sum
public import DomainTheory.Neighborhood.Exercise315
public import DomainTheory.Neighborhood.Exercise819.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u


section General

variable {α β γ δ : Type*}

/-- If `f` sends the master input to only the master output, then `f` sends `⊥` to `⊥`
(more precisely, `≤ ⊥`, i.e. `= ⊥` by `bot_le`). The elementwise membership at `⊥` is read off the
relation at `V₀.master` via `rel_iff_mem_principal` (`⊥ = ↑Δ`). -/
theorem toElementMap_bot_le {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (f : ApproximableMap V₀ V₁) (h : ∀ {Y}, f.rel V₀.master Y → Y = V₁.master) :
    f.toElementMap V₀.bot ≤ V₁.bot := by
  intro Y hY
  rw [mem_bot]
  exact h ((rel_iff_mem_principal f V₀.master_mem).mpr hY)

end General
end DomainTheory.Neighborhood
