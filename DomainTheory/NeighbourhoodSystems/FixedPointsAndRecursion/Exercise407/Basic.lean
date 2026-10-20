module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.fixAbove
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_step
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_mono

@[expose] public section

/-!
# Exercise 4.7 (Scott 1981, PRG-19, Lecture IV)

Formula 4.2(iii) gives the *least* fixed point `fix(f) = ⊔ₙ fⁿ(⊥)`. Suppose instead that
`a ∈ |𝒟|` satisfies `a ⊑ f(a)`. *Will there be a fixed point `x = f(x)` with `a ⊑ x`?*

**Yes.** Replace `⊥` by `a`: the chain `a ⊑ f(a) ⊑ f²(a) ⊑ …` is increasing (monotonicity of `f`
applied to `a ⊑ f(a)`), hence *directed*, so its union `x = ⊔ₙ fⁿ(a)` is a genuine element of `|𝒟|`
(Scott's hint: this is why `⊔` makes sense — directed unions of filters are filters, Exercise 2.11 /
`iSupDirected`). Approximable maps preserve directed unions (`toElementMap_iSupDirected`), which makes
`x` a fixed point, and `a = f⁰(a) ⊑ x` by construction. Moreover `x` is the *least* fixed point above
`a` (`fixAbove_least`), the relativized analogue of 4.2(iii).

All constructions are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap






end ApproximableMap
end DomainTheory.NeighbourhoodSystems
