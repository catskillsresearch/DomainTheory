/-ai
The elements of the infinite iterate are order-isomorphic to the elements of its product with the original domain, by the correspondence with sequences, the shift that splits off the first term, the product of the identity with the inverse sequence correspondence, and the inverse product equivalence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.component_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSeqEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.natShiftEquiv

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The isomorphism `|𝒟^∞| ≃o |𝒟 × 𝒟^∞|`, obtained from the
sequence correspondence and the shift. -/
def iterProdIso (V : NeighborhoodSystem α) :
    (iterSys V).Element ≃o (prod V (iterSys V)).Element :=
  (iterSeqEquiv V).trans <|
    (natShiftEquiv V.Element).trans <|
      (prodCongrOrderIso (OrderIso.refl V.Element) (iterSeqEquiv V).symm).trans
        (prodEquiv V (iterSys V)).symm

end DomainTheory.NeighbourhoodSystems
