/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


section General

variable {α β γ δ : Type*}

/-- The pairing of two bottoms is the bottom of the product. -/
theorem pair_bot {V0 : NeighborhoodSystem α} {V1 : NeighborhoodSystem β} :
    pair V0.bot V1.bot = (prod V0 V1).bot := by
  apply le_antisymm
  · intro W hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW
    rw [mem_bot] at hX hY
    subst hX; subst hY
    rw [mem_bot]
    exact prod_master.symm
  · exact NeighborhoodSystem.bot_le _ _

end General
end DomainTheory.NeighbourhoodSystems
