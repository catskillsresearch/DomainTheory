module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_zero
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_succ
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.funOf_botElem
public import DomainTheory.DataTypesAsLattices.Enumeration.condC_app2
public import DomainTheory.DataTypesAsLattices.Lambda.condC_more

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem cond_graph_eq_bot_iff (x y : Pomega) :
    funOf (funOf condC x) y = botElem ↔ x = botElem ∧ y = botElem := by
  constructor
  · intro h
    constructor
    · have := congrArg (fun w => funOf w (ofNat 0)) h
      rw [condC.beta3, eq_2_7_zero, funOf_botElem] at this
      exact this
    · have := congrArg (fun w => funOf w (ofNat 1)) h
      rw [condC.beta3, eq_2_7_succ, funOf_botElem] at this
      exact this
  · intro ⟨hx, hy⟩
    rw [condC_app2, hx, hy]
    ext p
    constructor
    · intro hp
      rcases hp with ⟨n, m, _, hm⟩
      simp [condSet, botElem] at hm
    · intro hp
      exact hp.elim

end DomainTheory.DataTypesAsLattices
