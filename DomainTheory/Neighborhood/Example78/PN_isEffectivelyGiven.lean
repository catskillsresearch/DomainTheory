/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.Example78.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Example78

open Domain.Recursive NeighborhoodSystem








/-- **Example 7.8 (Scott 1981, PRG-19).** The powerset domain `PN` is effectively given. -/
theorem PN_isEffectivelyGiven : PN.IsEffectivelyGiven := ⟨PNpres⟩

end DomainTheory.Neighborhood.Example78
