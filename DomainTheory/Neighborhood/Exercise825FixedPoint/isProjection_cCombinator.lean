/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition810b
public import DomainTheory.Neighborhood.Table55
public import DomainTheory.Neighborhood.Exercise823
public import DomainTheory.Neighborhood.Exercise715
public import DomainTheory.Neighborhood.Exercise825Pow
public import DomainTheory.Neighborhood.Exercise825Embed
public import DomainTheory.Neighborhood.Exercise825Closing
public import DomainTheory.Neighborhood.Exercise820
public import DomainTheory.Neighborhood.Exercise825FixedPoint.Basic
public import DomainTheory.Neighborhood.Exercise825FixedPoint.cInj_comp_cProj_le
public import DomainTheory.Neighborhood.Exercise825FixedPoint.isRetraction_cCombinator

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap







theorem isProjection_cCombinator : IsProjection cCombinator :=
  ⟨isRetraction_cCombinator, cInj_comp_cProj_le⟩

end DomainTheory.Neighborhood
