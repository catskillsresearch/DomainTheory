# Exercise 5.12

**EXERCISE 5.12.** On any domain $D$ introduce (as a least fixed point) a combinator

$$
\mathrm{while} : (D \to T) \times (D \to D) \to (D \to D)
$$

by the recursion

$$
\mathrm{while}(p, f)(x) = \mathrm{cond}(p(x), \mathrm{while}(p, f)(f(x)), x).
$$

Prove that

$$
\mathrm{while}(p, \mathrm{while}(p, f)) = \mathrm{while}(p, f).
$$

Show how $\mathrm{while}$ could have been used to obtain the least number operator mentioned in the proof of 5.6. Generalize the idea to define a combinator

$$
\mathrm{find} : D^\infty \times (D \to T) \to D
$$

with the meaning "find the first term of the sequence (if any) which satisfies the given precicate."

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512.lean](../Exercise512.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Wop.lean](Wop.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Wop_apply.lean](Wop_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/bodyMap.lean](bodyMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/bodyMap_apply.lean](bodyMap_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileFix.lean](whileFix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap.lean](whileMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_bot.lean](whileMap_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_false.lean](whileMap_false.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_least.lean](whileMap_least.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_rec.lean](whileMap_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_true.lean](whileMap_true.lean)
