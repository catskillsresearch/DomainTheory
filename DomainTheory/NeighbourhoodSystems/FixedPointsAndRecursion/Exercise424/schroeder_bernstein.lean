/-ai
Injections from A to B and from B to A yield a bijective map from A to B.

Tarski's map is a witness: it is injective because the first map is injective, and surjective because the second map is injective.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.Basic

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
