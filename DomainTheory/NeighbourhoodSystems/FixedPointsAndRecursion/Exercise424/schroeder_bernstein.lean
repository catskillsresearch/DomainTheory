module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbOp
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.schroeder_bernstein_equiv
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbOp_monotone
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet_isFixed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.mem_range_of_not_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.g_sbFun_not_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.g_f_mem_of_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun_injective
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun_surjective

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}


open Classical in


/-- **Exercise 4.24 (Scott 1981, PRG-19) — Schröder–Bernstein.** Injections `f : A → B` and
`g : B → A` yield a bijection `A → B`. -/
theorem schroeder_bernstein (hf : Injective f) (hg : Injective g) :
    ∃ h : A → B, Bijective h :=
  ⟨sbFun f g, sbFun_injective hf, sbFun_surjective hg⟩

end DomainTheory.NeighbourhoodSystems.Exercise424
