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

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Wop.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Wop.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Wop_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Wop_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/bodyMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/bodyMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/bodyMap_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/bodyMap_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileFix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileFix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_false.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_false.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_least.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_least.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_rec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_true.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_true.lean)
