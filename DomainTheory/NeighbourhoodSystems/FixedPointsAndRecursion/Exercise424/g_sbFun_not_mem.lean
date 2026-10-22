module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.mem_range_of_not_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

/-- Off the fixed set, `h(a)` is a genuine `g`-preimage of `a`: `g(h(a)) = a`. -/
theorem g_sbFun_not_mem {a : A} (ha : a ∉ sbSet f g) : g (sbFun f g a) = a := by
  rw [sbFun, dite_eq_right ha]
  exact Classical.choose_spec (mem_range_of_not_mem ha)

end DomainTheory.NeighbourhoodSystems.Exercise424
