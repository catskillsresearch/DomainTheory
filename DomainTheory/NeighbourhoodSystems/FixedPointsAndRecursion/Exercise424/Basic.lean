/-ai
This file gathers and re-exports Tarski's operator and its monotonicity, the fixed set and its fixed-point equation, the range lemma, Tarski's map and its values on and off the fixed set, the two mixed-membership lemmas, and injectivity and surjectivity of the map, together with the equivalence they determine. The module comment records that injections from A to B and from B to A yield a bijection, built from a fixed point of the operator sending a set to the complement of the range of the second injection united with the image of that set under the two maps, by using the first injection on the fixed set and a preimage under the second injection off it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
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

/-!
# Exercise 4.24 (Scott 1981, PRG-19, Lecture IV) — Schröder–Bernstein via a fixed point

(For set theorists.) Let `f : A → B` and `g : B → A` be one-one (injective, not necessarily onto).
**Then there is a one-one correspondence `h : A ≃ B`** (`schroeder_bernstein`).

Following Tarski's hint, work in the power-set domain `P A` (a complete lattice) and take a fixed
point `X` of the monotone operator

  `T(X) = (A − g(B)) ∪ g(f(X))`,

which exists by Knaster–Tarski (Exercise 4.14 / 4.13(2), here `lfpSet`). With `X = T(X)` fixed,
define

  `h(a) = f(a)`        if `a ∈ X`,
  `h(a) = g⁻¹(a)`      if `a ∉ X`

— well-defined because `a ∉ X = T(X)` forces `a ∈ g(B)` (it is not in `(A − g(B))`), so `a` has a
unique `g`-preimage (`mem_range_of_not_mem`). The map `h` is:

* **injective** (`sbFun_injective`): within `X`, by injectivity of `f`; outside `X`, by injectivity
  of `g`; the mixed case is impossible — `f(a₁) = g⁻¹(a₂)` would put `a₂ = g(f(a₁)) ∈ g(f(X)) ⊆ X`;
* **surjective** (`sbFun_surjective`): for `b ∈ B`, if `g(b) ∉ X` then `h(g(b)) = b`; if `g(b) ∈ X`
  then `g(b) ∈ g(f(X))`, so `g(b) = g(f(a))` with `a ∈ X`, whence `b = f(a) = h(a)`.

Packaged as the equivalence `schroeder_bernstein_equiv`. This is a *set theorists'* exercise and is
inherently classical; the construction of `h` uses `Classical.choice` (the `g`-preimage), exactly as
the statement demands.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}


end DomainTheory.NeighbourhoodSystems.Exercise424
