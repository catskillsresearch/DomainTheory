/-ai
This module gathers and re-exports the continuous-extension map and the embedding into Pω used for Theorems 1.5 and 1.6 of Scott 1976, §1, together with the topological background those constructions depend on.
ai-/
module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
import all Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
import all Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint
public import DomainTheory.DataTypesAsLattices.Embedding.extend
public import DomainTheory.DataTypesAsLattices.Embedding.embed

@[expose] public section

/-!
# Scott 1976, §1 — extension and embedding into `Pω`

Theorems 1.5 and 1.6.
-/

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function


end DomainTheory.DataTypesAsLattices
