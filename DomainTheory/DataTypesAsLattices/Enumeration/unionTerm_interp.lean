
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
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
  simpa [condC_beta3, Kcomb_beta] using union_via_cond x y

end DomainTheory.DataTypesAsLattices
