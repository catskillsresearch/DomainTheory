module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_pos
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.not_mem_zero_cond_graph
public import DomainTheory.DataTypesAsLattices.Enumeration.cond_graph_eq_bot_iff
public import DomainTheory.DataTypesAsLattices.Lambda.condC_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem eq_3_1 (x y : Pomega) :
    funOf (funOf (funOf condC x) y) (funOf (funOf condC x) y) = y := by
  rw [condC.beta3]
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
