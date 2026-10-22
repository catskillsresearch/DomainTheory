/-ai
Scott 1976, (3.1): applying the conditional of x and y to that same conditional yields y.

Rewrite by the three-argument beta law for the conditional. If both x and y are bottom, the conditional graph of two bottoms is bottom, and simplifying the conditional set at bottom gives bottom. Otherwise the conditional graph is distinct from bottom, since a bottom graph would force both arguments to be bottom, and 0 does not belong to the graph, so the remaining case of the conditional (2.7) returns y.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.not_mem_zero_cond_graph
public import DomainTheory.DataTypesAsLattices.Enumeration.cond_graph_eq_bot_iff

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (3.1).** `cond(x)(y)(cond(x)(y)) = y`. -/
theorem eq_3_1 (x y : Pomega) :
    funOf (funOf (funOf condC x) y) (funOf (funOf condC x) y) = y := by
  rw [condC_beta3]
  by_cases hxy : x = botElem ∧ y = botElem
  · rcases hxy with ⟨rfl, rfl⟩
    have : funOf (funOf condC botElem) botElem = botElem :=
      (cond_graph_eq_bot_iff botElem botElem).mpr ⟨rfl, rfl⟩
    simp [condSet, botElem]
  · have hne : funOf (funOf condC x) y ≠ botElem := by
      intro h
      exact hxy ((cond_graph_eq_bot_iff x y).mp h)
    exact eq_2_7_pos x y (funOf (funOf condC x) y)
      (not_mem_zero_cond_graph x y) hne

end DomainTheory.DataTypesAsLattices
