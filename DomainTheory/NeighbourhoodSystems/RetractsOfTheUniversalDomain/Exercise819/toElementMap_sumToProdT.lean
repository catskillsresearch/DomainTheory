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








section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


theorem toElementMap_sumToProdT (w : (sum E E hE hE).Element) :
    (sumToProdT hE).toElementMap w
      = pair ((whichMap E E hE hE).toElementMap w)
          (pair ((outMap₀ (h₀ := hE) (h₁ := hE)).toElementMap w)
            ((outMap₁ (h₀ := hE) (h₁ := hE)).toElementMap w)) := by
  simp only [sumToProdT, toElementMap_paired]

end Sum
end DomainTheory.NeighbourhoodSystems
