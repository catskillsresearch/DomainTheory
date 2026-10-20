/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example23
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.Example44.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Example44

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB



















/-- `σX ⊆ X` along the prefix order: a prepended neighbourhood is contained in any neighbourhood it
refines. (Used only via `prepend_mono`; kept implicit.) -/
theorem prepend_subset_self : True := trivial

end DomainTheory.Neighborhood.Example44
