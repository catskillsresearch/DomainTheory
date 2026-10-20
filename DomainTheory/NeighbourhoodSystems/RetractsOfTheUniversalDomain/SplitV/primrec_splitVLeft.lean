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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_splitVMinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_splitVBit

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive






















theorem primrec_splitVLeft : Nat.Primrec splitVLeft := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  have hpow : Nat.Primrec (fun n : ℕ => (2 : ℕ) ^ splitVBit n) := primrec_two_pow primrec_splitVBit
  exact (Nat.Primrec.pair hk1 hpow).of_eq fun n => rfl

end DomainTheory.NeighbourhoodSystems
