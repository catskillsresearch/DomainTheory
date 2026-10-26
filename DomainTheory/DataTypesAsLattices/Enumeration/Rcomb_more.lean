module

public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Rterm
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

namespace Rterm

theorem interp :
    _root_.DomainTheory.DataTypesAsLattices.interp Rterm (fun _ => botElem) = Rcomb := by
  unfold Rterm Rcomb
  apply congrArg graph
  funext x
  change _root_.DomainTheory.DataTypesAsLattices.interp (seq2Term .zero (.var 0))
      (envSet (fun _ => botElem) 0 x) =
    seq2 (ofNat 0) x
  rw [seq2Term.interp]
  · simp [_root_.DomainTheory.DataTypesAsLattices.interp, envSet, Function.update]
  · trivial
  · exact Nat.zero_ne_add_one 7

end Rterm

namespace Rcomb

theorem combinatory : IsCombinatory Rcomb := by
  rw [← Rterm.interp]
  exact theorem_2_4.closed Rterm

end Rcomb

end DomainTheory.DataTypesAsLattices
