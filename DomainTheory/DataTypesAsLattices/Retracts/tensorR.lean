/-ai
Scott 1976, (4.9). The product of two retracts is the graph of the map that pairs the first retract applied to the zeroth component with the second retract applied to the first component.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.9).** Product of retracts `a ⊗ b = λu. ⟨a(u₀), b(u₁)⟩`. -/
def tensorR (a b : Pomega) : Pomega :=
  graph (fun u =>
    pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))

end DomainTheory.DataTypesAsLattices
