# Exercise 5.7

What is *not* said in 5.6 is that every $\lambda$-term defines a partial recursive function. This is true (with suitable control over the constants and types in the expression), but the proof requires a full analysis of computability properties of domain constructions. This is the topic of Lecture VII.

It should be remarked that the types of variables needed for the proof of 5.6 never get very high. In fact, types like $N$, $N^k$, and $(N^k \to N)$ were the only ones needed (with perhaps $T$ thrown in also).

Recursion on $N$ was the topic of 5.6; further examples of recursion on other domains are included in the exercises.

## EXERCISES

**EXERCISE 5.7.** Find definitions of

$$\lambda x, y.\, \tau \quad \text{and} \quad \sigma(x, y)$$

which use only $\lambda v$ with one variable and applications only to one argument at a time. Note that use must be made of the combinators $p_0$, $p_1$, pair. Generalize the result to functions of many variables.

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507.lean](../Exercise507.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/app_two_args.lean](app_two_args.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/curryu2083_apply.lean](curryu2083_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/curry₃.lean](curry₃.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/lam_two_vars.lean](lam_two_vars.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/surjective_pairing.lean](surjective_pairing.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/uncurry_apply.lean](uncurry_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/uncurry_lam_two_vars.lean](uncurry_lam_two_vars.lean)
