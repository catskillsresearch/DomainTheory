/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.ExampleB
public import DomainTheory.Neighborhood.Example23
public import DomainTheory.Neighborhood.Theorem75
public import DomainTheory.Neighborhood.Exercise724.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise724

open NeighborhoodSystem Domain.Recursive















































































































/-- `embStr` is injective. -/
theorem embStr_injective : Function.Injective embStr :=
  List.map_injective_iff.mpr bitToNat_injective

end DomainTheory.Neighborhood.Exercise724
