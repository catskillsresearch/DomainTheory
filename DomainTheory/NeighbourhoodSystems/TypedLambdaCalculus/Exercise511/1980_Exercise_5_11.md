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

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_tail.lean](component_tail.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/diag_rec.lean](diag_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/fold.lean](fold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/fold_unfold.lean](fold_unfold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/iterProdIso_apply.lean](iterProdIso_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapBody_apply.lean](mapBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/map_rec.lean](map_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/push.lean](push.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/push_head_tail.lean](push_head_tail.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/unfold.lean](unfold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head.lean](head.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head_apply.lean](head_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail.lean](tail.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail_apply.lean](tail_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/Arg.lean](Arg.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/diag.lean](diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapBody.lean](mapBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapOp.lean](mapOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapMap.lean](mapMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/unfold_fold.lean](unfold_fold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head_push.lean](head_push.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail_push.lean](tail_push.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_diag.lean](component_diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_map.lean](component_map.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511.lean](../Exercise511.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/T_bot_eq.lean](../Theorem56Full/T_bot_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/argElem_argLike.lean](../Theorem56Full/argElem_argLike.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_argElem_none.lean](../Theorem56Full/component_argElem_none.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_bot.lean](../Theorem56Full/component_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_push_succ.lean](../Theorem56Full/component_push_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_push_zero.lean](../Theorem56Full/component_push_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_vecElem_lt.lean](../Theorem56Full/component_vecElem_lt.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/eq_of_component_eq.lean](../Theorem56Full/eq_of_component_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/evalAt_apply.lean](../Theorem56Full/evalAt_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findBody_apply.lean](../Theorem56Full/findBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findOp_iterElem_zero.lean](../Theorem56Full/findOp_iterElem_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_apply.lean](../Theorem56Full/guard1_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_bot.lean](../Theorem56Full/guard1_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_inner_bot.lean](../Theorem56Full/guard1_inner_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_total.lean](../Theorem56Full/guard1_total.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/iterVal_succ.lean](../Theorem56Full/iterVal_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_coe_val.lean](../Theorem56Full/lamDef_coe_val.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_congr.lean](../Theorem56Full/lamDef_congr.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/mem_mOfFn.lean](../Theorem56Full/mem_mOfFn.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/oneArg_bot.lean](../Theorem56Full/oneArg_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/optElem.lean](../Theorem56Full/optElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/precBody_apply.lean](../Theorem56Full/precBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/push_natElem_vecElem.lean](../Theorem56Full/push_natElem_vecElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findMap_vecElem.lean](../Theorem56Full/findMap_vecElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/oneArg_natElem.lean](../Theorem56Full/oneArg_natElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/realizer_value.lean](../Theorem56Full/realizer_value.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recMap_rec.lean](../Theorem56Full/recMap_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recMap_eval.lean](../Theorem56Full/recMap_eval.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_rec.lean](../Theorem56Full/searchMap_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_step_found.lean](../Theorem56Full/searchMap_step_found.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_step_next.lean](../Theorem56Full/searchMap_step_next.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_climb.lean](../Theorem56Full/searchMap_climb.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/strictGuardN_strict.lean](../Theorem56Full/strictGuardN_strict.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/strictGuardN_total.lean](../Theorem56Full/strictGuardN_total.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/toApproxMap_bot.lean](../Theorem56Full/toApproxMap_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/iterVal_zero.lean](../Theorem56Full/iterVal_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/iterVal_bot.lean](../Theorem56Full/iterVal_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_diverge.lean](../Theorem56Full/searchMap_diverge.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_succ.lean](../Theorem56Full/tupleMap_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_tupleMap.lean](../Theorem56Full/component_tupleMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_zero.lean](../Theorem56Full/tupleMap_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_tupleMap_ge.lean](../Theorem56Full/component_tupleMap_ge.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_argLike.lean](../Theorem56Full/tupleMap_argLike.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_vecElem_eq.lean](../Theorem56Full/tupleMap_vecElem_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/vecElem_totals.lean](../Theorem56Full/vecElem_totals.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_of_inner.lean](../Theorem56Full/lamDef_of_inner.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_comp.lean](../Theorem56Full/lamDef_comp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_prec.lean](../Theorem56Full/lamDef_prec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_primComp.lean](../Theorem56Full/lamDef_primComp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_rfind.lean](../Theorem56Full/lamDef_rfind.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_total.lean](../Theorem56Full/lamDef_total.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_get.lean](../Theorem56Full/lamDef_get.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_succ.lean](../Theorem56Full/lamDef_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_zero.lean](../Theorem56Full/lamDef_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/primrec_lamDef.lean](../Theorem56Full/primrec_lamDef.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/partrec_lamDef.lean](../Theorem56Full/partrec_lamDef.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full.lean](../Theorem56Full.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/partrec_one.lean](../Theorem56Full/partrec_one.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/𝒩.lean](../Theorem56Full/𝒩.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/ArgLike.lean](../Theorem56Full/ArgLike.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/argElem.lean](../Theorem56Full/argElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/vecElem.lean](../Theorem56Full/vecElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/LamDef.lean](../Theorem56Full/LamDef.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_argElem.lean](../Theorem56Full/component_argElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_vecElem.lean](../Theorem56Full/component_vecElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/evalAt.lean](../Theorem56Full/evalAt.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findBody.lean](../Theorem56Full/findBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findOp.lean](../Theorem56Full/findOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1.lean](../Theorem56Full/guard1.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/oneArg.lean](../Theorem56Full/oneArg.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/precBody.lean](../Theorem56Full/precBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recOp.lean](../Theorem56Full/recOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recMap.lean](../Theorem56Full/recMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/rfindZeroPred.lean](../Theorem56Full/rfindZeroPred.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap.lean](../Theorem56Full/searchMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findMap.lean](../Theorem56Full/findMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/strictGuardN.lean](../Theorem56Full/strictGuardN.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap.lean](../Theorem56Full/tupleMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/Basic.lean](../Theorem56Full/Basic.lean)
