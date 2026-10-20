/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_myXor
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myAndNot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_myAndNot : Nat.Primrec (fun t => myAndNot t.unpair.1 t.unpair.2) := by
  have hland : Nat.Primrec (fun t : ℕ => myLand t.unpair.1 t.unpair.2) := primrec_myLand
  exact (primrec_myXor.comp (Nat.Primrec.left.pair hland)).of_eq fun t => by
    simp only [myAndNot, unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
