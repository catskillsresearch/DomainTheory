/-ai
The image of an element under the successor map for a bit b is disjoint from the copy for a different bit.

A membership witness would supply a point of a neighbourhood of the element whose prepended copy lies in the other bit embedding. Equality of cons cells would force the bits to agree.
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

/-- `(b·z)` never meets the `(¬b)`-copy: `0z` avoids the `1`-copies and vice versa (used to discharge
the cross-tag cases in `toCC_consMap`). -/
theorem consMap_not_mem_embBit_ne {b c : Bool} (hbc : b ≠ c) {z : C.Element} {X : Set Str} :
    ¬ ((consMap b).toElementMap z).mem (embBit c X) := by
  rintro ⟨X', hzX', hX'mem, _, hsub⟩
  obtain ⟨a, ha⟩ := C_nonempty X' hX'mem
  rw [← embBit_eq_prepend] at hsub
  obtain ⟨w, hw, heq⟩ := hsub ⟨a, rfl, ha⟩
  rw [List.cons.injEq] at hw; exact hbc hw.1

end Example62C

end DomainTheory.NeighbourhoodSystems
