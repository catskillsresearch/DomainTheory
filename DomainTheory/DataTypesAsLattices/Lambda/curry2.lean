module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def curry2 (f : Pomega → Pomega → Pomega)
    (_hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (_hfy : ∀ x, IsScottContinuous (fun y => f x y)) : Pomega :=
  graph (fun x => graph (fun y => f x y))

end DomainTheory.DataTypesAsLattices
