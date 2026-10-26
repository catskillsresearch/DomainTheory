
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_beta
public import DomainTheory.DataTypesAsLattices.Lambda.condC_beta3
public import DomainTheory.DataTypesAsLattices.Lambda.union_via_cond
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.unionTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem unionTerm_interp :
    interp unionTerm (fun _ => botElem) =
      graph (fun x => graph (fun y => x ∪ y)) := by
  unfold unionTerm
  simp only [interp, envSet, Function.update_self]
  apply congrArg graph
  funext x
  apply congrArg graph
  funext y
  change condSet (graph fun _ => zeroC) x y = x ∪ y
  simpa [condC.beta3, Kcomb_beta] using union_via_cond x y

end DomainTheory.DataTypesAsLattices
