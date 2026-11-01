module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def updateEnv (t x : Pomega) (n : ℕ) : Pomega :=
  graph (fun m => if m = ofNat n then x else funOf t m)

end DomainTheory.DataTypesAsLattices
