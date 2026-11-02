
module

public import Mathlib.Topology.Bases
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem beta {τ : Pomega → Pomega} (hτ : IsScottContinuous τ) (y : Pomega) :
    funOf (lam τ) y = τ y := by
  simp [lam, theorem_1_2.i hτ]

end DomainTheory.DataTypesAsLattices
