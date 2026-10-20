/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise826
public import DomainTheory.Neighborhood.Exercise821
public import DomainTheory.Neighborhood.Exercise827.Basic
public import DomainTheory.Neighborhood.Exercise827.toElementMap_piDTypeMap

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap






















































theorem isFinitaryProjection_piDType (d : ApproximableMap U U) (s : U.Element) :
    IsFinitaryProjection (piDType d s) := by
  unfold piDType
  rw [toElementMap_piDTypeMap]
  exact isFinitaryProjection_decode_subU (d.toElementMap s)

end DomainTheory.Neighborhood
