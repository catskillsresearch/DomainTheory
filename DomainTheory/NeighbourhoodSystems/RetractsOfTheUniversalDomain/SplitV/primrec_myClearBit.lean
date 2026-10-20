/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive











theorem primrec_myClearBit : Nat.Primrec (fun t => myClearBit t.unpair.1 t.unpair.2) := by
  have hpow : Nat.Primrec (fun t : ℕ => (2 : ℕ) ^ t.unpair.2) := primrec_two_pow Nat.Primrec.right
  exact (primrec_sub₂ Nat.Primrec.left hpow).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems
