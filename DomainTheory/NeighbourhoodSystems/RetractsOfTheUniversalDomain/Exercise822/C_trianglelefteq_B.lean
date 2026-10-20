/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example62
public import DomainTheory.Neighborhood.Example44
public import DomainTheory.Neighborhood.Lemma615
public import DomainTheory.Neighborhood.Exercise822.Basic
public import DomainTheory.Neighborhood.Exercise822.C_isomorphic_Du27

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822
















































/-- **`C ⊴ B`.** The nontrivial half of Exercise 8.22: `C` (finite-or-infinite binary sequences)
embeds as a subdomain of `B` (infinite binary sequences) via the bit-doubling re-encoding
`enc`/`encC` and the image subsystem `D' ◁ B`. -/
theorem C_trianglelefteq_B : C ⊴ B := ⟨D', D'_subsystem_B, C_isomorphic_D'⟩

end Exercise822
end DomainTheory.Neighborhood
