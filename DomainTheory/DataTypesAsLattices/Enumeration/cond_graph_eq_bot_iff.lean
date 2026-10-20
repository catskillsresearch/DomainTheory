module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.condC_app2

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices





theorem cond_graph_eq_bot_iff (x y : Pomega) :
    funOf (funOf condC x) y = botElem ↔ x = botElem ∧ y = botElem := by
  constructor
  · intro h
    constructor
    · have := congrArg (fun w => funOf w (ofNat 0)) h
      rw [condC_beta3, eq_2_7_zero, funOf_botElem] at this
      exact this
    · have := congrArg (fun w => funOf w (ofNat 1)) h
      rw [condC_beta3, eq_2_7_succ, funOf_botElem] at this
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
