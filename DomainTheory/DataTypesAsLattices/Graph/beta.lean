
module

public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.IsGraph
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem beta {τ : Pomega → Pomega} (hτ : IsScottContinuous τ) (y : Pomega) :
    funOf (lam τ) y = τ y := by
  simp [lam, theorem_1_2.i hτ]

end DomainTheory.DataTypesAsLattices
