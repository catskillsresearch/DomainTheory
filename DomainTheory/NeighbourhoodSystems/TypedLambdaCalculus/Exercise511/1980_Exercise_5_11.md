# Exercise 5.11

**EXERCISE 5.11.** For any domain $\mathcal{D}$ we may regard $\mathcal{D}^\infty$ as consisting of (bottomless) *stacks* of elements of $\mathcal{D}$. With this image in mind, define appropriate combinators with the obvious meanings:

$$
\mathrm{head} : \mathcal{D}^\infty \to \mathcal{D};\quad
\mathrm{tail} : \mathcal{D}^\infty \to \mathcal{D}^\infty;\quad
\mathrm{push} : \mathcal{D} \times \mathcal{D}^\infty \to \mathcal{D}^\infty.
$$

Using the fixed-point theorem argue that there is a combinator

$$
\mathrm{diag} : \mathcal{D} \to \mathcal{D}^\infty
$$

where for all $x \in |\mathcal{D}|$ we have

$$
\mathrm{diag}(x) = \langle x \rangle_{n=0}^\infty.
$$
(Hint: Try a recursive definition, say

$$
\mathrm{diag}(x) = \mathrm{push}(x, \mathrm{diag}(x)),
$$

but be sure to prove *all* terms of $\mathrm{diag}(x)$ equal $x$.) Also introduce by an appropriate recursion a combinator

$$
\mathrm{map} : (D \to D)^\infty \times D \to D^\infty
$$

where for elements of the suitable types:

$$
\mathrm{map}(\langle f_n \rangle_{n=0}^\infty, x) = \langle f_n(x) \rangle_{n=0}^\infty.
$$

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511.lean](../Exercise511.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/Arg.lean](Arg.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_diag.lean](component_diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_map.lean](component_map.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_tail.lean](component_tail.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/diag.lean](diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/diag_rec.lean](diag_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/fold.lean](fold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/fold_unfold.lean](fold_unfold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head.lean](head.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head_apply.lean](head_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head_push.lean](head_push.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/iterProdIso_apply.lean](iterProdIso_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapBody.lean](mapBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapBody_apply.lean](mapBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapMap.lean](mapMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapOp.lean](mapOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/map_rec.lean](map_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/push.lean](push.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/push_head_tail.lean](push_head_tail.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail.lean](tail.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail_apply.lean](tail_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail_push.lean](tail_push.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/unfold.lean](unfold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/unfold_fold.lean](unfold_fold.lean)
