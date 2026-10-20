module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_beta2
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_beta2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































theorem SKK_eq_I : funOf (funOf Scomb Kcomb) Kcomb = graph (fun x => x) := by
  rw [Scomb_beta2]
  apply congrArg graph
  funext x
  simp [Kcomb_beta2]


end DomainTheory.DataTypesAsLattices
