# Exercise 5.9

**EXERCISE 5.9.** Suppose that $f, g : \mathcal{D} \to \mathcal{D}$ are approximable and $f \circ g = g \circ f$. Show that $f$ and $g$ have a *least common fixed point* $x = f(x) = g(x)$. (Hint: Refer back to Exercise 4.20.) If in addition $f(\bot) = g(\bot)$, show that $\mathrm{fix}(f) = \mathrm{fix}(g)$. In particular, will $\mathrm{fix}(f) = \mathrm{fix}(f^2)$? What if we only assume $f \circ g = g^2 \circ f$?

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/commute_apply.lean](commute_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/commuting_least_common_fixed.lean](commuting_least_common_fixed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/iterElem_le_fixElement.lean](iterElem_le_fixElement.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/iterElem_succ.lean](iterElem_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/iterElem_zerou27.lean](iterElem_zerou27.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/comp_self_iterElem.lean](comp_self_iterElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/fixElement_eq_of_commuting_bot.lean](fixElement_eq_of_commuting_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/fixElement_iterTwice.lean](fixElement_iterTwice.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509.lean](../Exercise509.lean)
