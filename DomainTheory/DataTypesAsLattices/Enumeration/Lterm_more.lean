module

public import DomainTheory.DataTypesAsLattices.Enumeration.Lterm
public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace Lterm

theorem interp : DomainTheory.DataTypesAsLattices.interp Lterm (fun _ => botElem) = Lcomb := by
  unfold Lterm Lcomb
  simp [DomainTheory.DataTypesAsLattices.interp, envSet, Function.update, succSet.ofNat]

end Lterm

end DomainTheory.DataTypesAsLattices
