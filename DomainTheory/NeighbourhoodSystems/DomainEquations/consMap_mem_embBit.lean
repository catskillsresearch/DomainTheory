/-ai
The image of an element z under the successor map for a bit b meets the b-copy of a neighbourhood X exactly when z meets X.

A membership witness is a neighbourhood of z contained in the prepended copy. That copy equals the bit embedding, so upward closure puts X in z. If z meets X, the same neighbourhood, the subneighbourhood of z, and membership of the bit embedding are a witness, again because the bit embedding equals the prepended copy.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ccEquiv_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Example62C

open Example44 ExampleB Example62

/-- `(b·z).mem (bX) ↔ z.mem X`: the `b`-successor's filter restricted to the `b`-copy is `z`. -/
theorem consMap_mem_embBit {b : Bool} {z : C.Element} {X : Set Str} (hX : C.mem X) :
    ((consMap b).toElementMap z).mem (embBit b X) ↔ z.mem X := by
  constructor
  · rintro ⟨X', hzX', _, _, hsub⟩
    rw [← embBit_eq_prepend] at hsub
    exact z.up_mem hzX' hX (embBit_subset.mp hsub)
  · intro hz
    refine ⟨X, hz, z.sub hz, memC_embBit b hX, ?_⟩
    rw [← embBit_eq_prepend]

end Example62C

end DomainTheory.NeighbourhoodSystems
