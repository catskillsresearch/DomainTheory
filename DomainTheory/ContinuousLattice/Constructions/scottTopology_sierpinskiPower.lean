module

public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.Constructions.scottTopology_prop
public import DomainTheory.ContinuousLattice.Constructions.proposition_2_9
public import DomainTheory.ContinuousLattice.Constructions.isContinuousLattice_prop
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


/-- The Scott topology on a power `ι → 𝕆` of the Sierpiński space coincides with the product
(= Sierpiński power) topology. Combine Proposition 2.9(b) (the Scott topology of a product is the
product of the factors' Scott topologies) with `scottTopology_prop` (each factor's Scott topology
is the Sierpiński topology). -/
theorem scottTopology_sierpinskiPower (ι : Type*) :
    (scottTopologicalSpace : TopologicalSpace (ι → Prop)) =
      (inferInstance : TopologicalSpace (ι → Prop)) := by
  rw [(proposition_2_9 (fun _ => Prop) (fun _ => isContinuousLattice_prop)).2]
  show (@Pi.topologicalSpace ι (fun _ => Prop) (fun _ => scottTopologicalSpace)) =
    @Pi.topologicalSpace ι (fun _ => Prop) (fun _ => sierpinskiSpace)
  congr 1
  funext _
  exact scottTopology_prop

end DomainTheory.ContinuousLattice
