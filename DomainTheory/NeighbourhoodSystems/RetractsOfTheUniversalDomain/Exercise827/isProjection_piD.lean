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
public import DomainTheory.Neighborhood.Exercise827.isRetraction_piD
public import DomainTheory.Neighborhood.Exercise827.le_idMap_piD

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap
































/-- **Scott's own hint, in full: `Π(d)` is a projection, for every `d`.** -/
theorem isProjection_piD (d : ApproximableMap U U) : IsProjection (piD d) :=
  ⟨isRetraction_piD d, le_idMap_piD d⟩

end DomainTheory.Neighborhood
