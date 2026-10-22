/-ai
The universe combinator is a retract: it equals the graph of a ↦ the combinator applied to the combinator applied to a.

Two graphs agree when their bodies agree. The application formula says that the combinator applied to a is the graph of x ↦ V(a)(x), and equation (5.19) says that applying the combinator twice does not change that value.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_19

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Vcomb_isRetract : IsRetract Vcomb := by
  change Vcomb = graph (fun a => funOf Vcomb (funOf Vcomb a))
  apply graph_ext
  intro a
  exact (Vcomb_app a).symm.trans (eq_5_19 a).symm

end DomainTheory.DataTypesAsLattices
