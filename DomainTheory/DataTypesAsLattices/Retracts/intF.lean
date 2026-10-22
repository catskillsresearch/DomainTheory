module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.7).** The integer functional
`int(u) = u ⊒ 0, (int(u−1) ⊒ u, u)`. -/
def intF (f : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u))

end DomainTheory.DataTypesAsLattices
