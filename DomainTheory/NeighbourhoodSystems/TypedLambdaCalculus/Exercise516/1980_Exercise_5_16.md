# Exercise 5.16

**EXERCISE 5.16.** Return to the discussion of Example 4.4 and the construction of the domain of finite and infinite binary sequences. Give a fixed-point definition of $\mathrm{neg} : C \to C$, where

$$
\mathrm{neg}(0x) = 1\,\mathrm{neg}(x); \qquad \mathrm{neg}(1x) = 0\,\mathrm{neg}(x).
$$

Prove that $\mathrm{neg}(\mathrm{neg}(x)) = x$ for all $x \in |C|$. Also define $\mathrm{merge} : C \times C \to C$, where for $\epsilon, \delta \in \{0, 1\}$ we have:

$$
\mathrm{merge}(\epsilon x, \delta y) = \epsilon\,\delta\,\mathrm{merge}(x, y).
$$

(Note: There may be a little trouble with $\mathrm{merge}(x, y)$ when $x$ is finite and total and $y$ is infinite—you have to decide what you want in e.g. $\mathrm{merge}(\Lambda, y)$.) Prove that

$$
\mathrm{merge}(x, x) = d(x),
$$

in the notation of 4.4. Consider also the infinite non-periodic sequence

$$
t = 0\,\mathrm{merge}(\mathrm{neg}(t), \mathrm{tail}(t)).
$$

Prove that the $n^{\mathrm{th}}$ digit of $t$ is the sum mod 2 of the digits of the number $n$ written in the binary scale (a suggestion of J. Lambek). Show also that $t \neq u\,a\,a\,a\,v$ where $a$ is any finite sequence $\neq \Lambda$, and where $u$ is finite.

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe_cons2.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe_cons2.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe_cons_inv.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe_cons_inv.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap_strElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap_strElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/d_hcone.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/d_hcone.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/d_hsing.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/d_hsing.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_append.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_append.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_prefix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_prefix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_flip.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_flip.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_prefix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_prefix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/map_ext_C.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/map_ext_C.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/memC_eq_shape.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/memC_eq_shape.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/memC_shape.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/memC_shape.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem_diag.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem_diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem_mono.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem_mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_diag.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_pair.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_pair.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_SLe.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_SLe.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_cons_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_cons_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_cons_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_cons_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_diag.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_comp_negMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_comp_negMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_negMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_negMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_strElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_strElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_cons_false.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_cons_false.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_cons_true.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_cons_true.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_hcone.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_hcone.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_hsing.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_hsing.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/not_strElem_le_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/not_strElem_le_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/prodMap_ext.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/prodMap_ext.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/prod_principal_pair.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/prod_principal_pair.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_false.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_false.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_le_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_le_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_true.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_true.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape_injective.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape_injective.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape_refine.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape_refine.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strBot_le_strBot_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strBot_le_strBot_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strBot_le_strElem_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strBot_le_strElem_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strElem_le_strElem_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strElem_le_strElem_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_consMap_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_consMap_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_consMap_strElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_consMap_strElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_strElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_strElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailSing.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailSing.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_hcone.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_hcone.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_hsing.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_hsing.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_prefix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_prefix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/Overlap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/Overlap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/append_three_period.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/append_three_period.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_cube.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_cube.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_overlap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_overlap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_three_consec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_three_consec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/odd_of_consec_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/odd_of_consec_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tElt_cube_free.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tElt_cube_free.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tmList_getElemu3f.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tmList_getElemu3f.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_of_eq_two_mul.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_of_eq_two_mul.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_of_eq_two_mul_add_one.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_of_eq_two_mul_add_one.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_two_mul_ne.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_two_mul_ne.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/cone_univ_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/cone_univ_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_append.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_append.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_iterate_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_iterate_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_tmList.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_tmList.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_le_fixElement.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_le_fixElement.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_succ_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_succ_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_zerou27.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_zerou27.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterate_expand_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterate_expand_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/mergeVal_snd_false.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/mergeVal_snd_false.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/strBot_mem_cone.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/strBot_mem_cone.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/strBot_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/strBot_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_digit.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_digit.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_mem_cone_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_mem_cone_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_unfold.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_unfold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_le_tElt.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_le_tElt.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_length.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_length.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_prefix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_prefix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp_strBot_expand.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp_strBot_expand.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_two_mul.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_two_mul.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_two_mul_add_one.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_two_mul_add_one.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/weave_head.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/weave_head.lean)
