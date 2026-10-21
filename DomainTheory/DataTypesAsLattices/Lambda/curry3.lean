/-ai
The curried form of a ternary map f is the graph of x ↦ the graph of y ↦ the graph of z ↦ f(x, y, z).
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

def curry3 (f : Pomega → Pomega → Pomega → Pomega)
    (_hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (_hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (_hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => f x y z)))

end DomainTheory.DataTypesAsLattices
