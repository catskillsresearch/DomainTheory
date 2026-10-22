# Theorem 7.5

Products give us a way of providing an immediate meaning to the notion of a computable function of several variables. Note that the proof of 3.7 is “effective” and shows that substitution of computable functions of several variables into each other always gives computable functions. We turn next to the function spaces.

**THEOREM 7.5.** If $\mathcal{D}_0$ and $\mathcal{D}_1$ are effectively given, then so is $(\mathcal{D}_0 \to \mathcal{D}_1)$. The combinators eval and curry are computable, provided all the domains involved are effectively given. The computable elements $f \in |\mathcal{D}_0 \to \mathcal{D}_1|$ are exactly the computable maps $f : \mathcal{D}_0 \to \mathcal{D}_1$.

*Proof:* The proofs of 3.9, 3.11, and 3.12 were set up with this theorem in mind. If
$$
\mathcal{D}_0 = \{ X_n \mid n \in \mathbf{N} \} \quad \text{and} \quad \mathcal{D}_1 = \{ Y_m \mid m \in \mathbf{N} \}
$$
are two effectively given neighbourhood systems, then the neighbourhoods of $(\mathcal{D}_0 \to \mathcal{D}_1)$, by Definition 3.8, are non-empty intersections like
$$
\bigcap_{i < q} [X_{n_i}, Y_{m_i}],
$$
where $\langle n_0, n_1, \ldots, n_{q-1} \rangle$ and $\langle m_0, m_1, \ldots, m_{q-1} \rangle$ are two finite sequences of integers determining the choice of the function-space neighbourhood. In 3.9(i) the test for nonemptiness is given. Assuming the decidability of relations in $\mathcal{D}_0$ and $\mathcal{D}_1$, one remarks that the consistency of *finite sequences* of neighbourhoods is also decidable. (Hint: Test the first *two*, then form their intersection. Next test the third given neighbourhood against this one set; if consistent, form the intersection, and carry on.) By 3.9(i) at most $2 \cdot 2^q$ such sequential checks must be carried out to determine whether the function-space neighbourhood is non empty.
It may not be fun, but the checks can be carried out in finite time. Owing to this decidability, we can therefore enumerate in a systematic way *all* the pairs of finite sequences $\langle n_0, \ldots \rangle$ and $\langle m_0, \ldots \rangle$ that determine neighbourhoods: that is the way that $(\mathcal{D}_0 \to \mathcal{D}_1)$ obtains its enumeration.

Concerning the decidability of the required relations on $(\mathcal{D}_0 \to \mathcal{D}_1)$, we remark first off that consistency is more of the same: to test two finite intersections against each other, just form one big intersection and test it for non-emptiness as before. Secondly, the testing for intersection comes down in the end to testing one typical intersection of $[X, Y]$-neighbourhoods for equality with another. But equality amounts to two inclusions; inclusion in an intersection amounts to inclusion in each term. Therefore, what we need to do is to check a finite number of statements of the form:

$$\bigcap_{i < q} [X_{n_i}, Y_{m_i}] \subseteq [X_k, Y_\ell].$$

As we pointed out after the proof of 3.9, this inclusion is equivalent to

$$\bigcap \{ Y_{m_i} \mid X_k \subseteq X_{n_i} \} \subseteq Y_\ell.$$

By decidability in $\mathcal{D}_0$, we can effectively find the $n_i$ that are needed. Then in $\mathcal{D}_1$, we form the intersection of the corresponding $Y_{m_i}$. Finally, we check the inclusion. Again, one check in $(\mathcal{D}_0 \to \mathcal{D}_1)$ requires a whole sequence of checks in $\mathcal{D}_0$ and in $\mathcal{D}_1$, but the process is finite. So we have argued that $(\mathcal{D}_0 \to \mathcal{D}_1)$ is effectively given.

In showing that the combinators are computable, we refer first to the proof of 3.11. The typical pair of neighbourhoods possibly belonging to eval is

$$\bigcap_{i < q} [X_{n_i}, Y_{m_i}], \ X_k \text{ eval } Y_\ell.$$

As we needed not to be so specific, we expressed the holding of this relationship in terms of *all* the functions in the function-
space neighbourhood. But we know that the neighbourhood, by 3.9(ii), has a minimal element; it is then sufficient to test for the holding of $X_k f_0 Y_\ell$ at this minimal function $f_0$. But this test, we have already seen, is decidable. So the pairs in eval actually form a recursive set, not just a recursively enumerable set; thus, eval is a computable function.

The case of curry involves three domains and is a bit more messy. But again, if the required neighbourhoods are written out in full, it will be seen that curry, too, is computable. We leave this minor struggle to the exercises.

The final statement is an easy consequence of the fundamental connection between approximable $f : \mathcal{D}_0 \to \mathcal{D}_1$ as relations and as elements. Recall, as in the proof of 3.10, that we have

$$f \in [X, Y] \text{ iff } X f Y,$$

for all $X \in \mathcal{D}_0$ and $Y \in \mathcal{D}_1$. Therefore,

$$f \in \bigcap_{i < q} [X_{n_i}, Y_{m_i}] \text{ iff } \forall i < q.\, X_{n_i} f Y_{m_i}.$$

It follows that if $f$ is recursively enumerable as a set of pairs, then, by forming all the non-empty intersections (as shown), we get an enumeration of all the neighbourhoods to which $f$ belongs; and this is the same as the filter corresponding to $f$ as an element of the function space. The converse direction is clear. $\square$

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList.lean](interList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList_nil.lean](interList_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair.lean](funPair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair_fst.lean](funPair_fst.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair_snd.lean](funPair_snd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/bitSelect.lean](bitSelect.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/bitSelect_nil.lean](bitSelect_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/andFoldl_eq_one_iff.lean](andFoldl_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/andFoldl_one.lean](andFoldl_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStep.lean](appendStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStp.lean](appendStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendCode.lean](appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStp_eq.lean](appendStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/botMap.lean](botMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/botMap_rel.lean](botMap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet.lean](condSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_nil.lean](condSet_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_subset.lean](condSet_subset.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consPairChar.lean](consPairChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consUpd.lean](consUpd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consStp.lean](consStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consCharAt.lean](consCharAt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_appendStep.lean](decodeList_appendStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_encodeList.lean](decodeList_encodeList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_foldl_appendStp.lean](decodeList_foldl_appendStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_appendCode.lean](decodeList_appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funImpChar.lean](funImpChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funConsChar.lean](funConsChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf.lean](funListOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum.lean](Xenum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_neg.lean](Xenum_neg.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_pos.lean](Xenum_pos.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_cons.lean](funListOf_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/exists_funListOf.lean](exists_funListOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_valid.lean](funListOf_valid.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_mem.lean](Xenum_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_nonempty.lean](Xenum_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/idxchain.lean](idxchain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interFrom.lean](interFrom.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interIdx.lean](interIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsStp.lean](interYsStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsIdx.lean](interYsIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_condSet.lean](mem_condSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_cons_neg.lean](condSet_cons_neg.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_cons_pos.lean](condSet_cons_pos.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condFoldl_spec.lean](condFoldl_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_eq_interYs.lean](condSet_eq_interYs.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_appendCode.lean](primrec_appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_consPairChar.lean](primrec_consPairChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interIdx.lean](primrec_interIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interYsStp.lean](primrec_interYsStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interYsIdx.lean](primrec_interYsIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/rel_interYs_funList.lean](rel_interYs_funList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYs_funList_mem_of_nonempty.lean](interYs_funList_mem_of_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/selectFn_isOne.lean](selectFn_isOne.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsIdx_spec.lean](interYsIdx_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/selectFn_mul_iff.lean](selectFn_mul_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_appendCode.lean](stepFun_funListOf_appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_inter_eq.lean](Xenum_inter_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consPairChar_spec.lean](consPairChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_eq_univ_iff.lean](stepFun_funListOf_eq_univ_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_subset_iff.lean](stepFun_funListOf_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subStp.lean](subStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_subStp.lean](primrec_subStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subChar.lean](subChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_subChar.lean](primrec_subChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subChar_spec.lean](subChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivStp.lean](trivStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_trivStp.lean](primrec_trivStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivialChar.lean](trivialChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/eqEnumChar.lean](eqEnumChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interEqChar.lean](interEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_trivialChar.lean](primrec_trivialChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_eqEnumChar.lean](primrec_eqEnumChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interEqChar.lean](primrec_interEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivialChar_spec.lean](trivialChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/eqEnumChar_spec.lean](eqEnumChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interEqChar_spec.lean](interEqChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPresentation.lean](funPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_singleton.lean](Xenum_singleton.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consChain_iff.lean](consChain_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/evalMap_rel_prodNbhd_iff.lean](evalMap_rel_prodNbhd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/evalMap_isComputable.lean](evalMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_append.lean](funListOf_append.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList_subset_base.lean](interList_subset_base.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_Xenum_iff.lean](mem_Xenum_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_isComputableElement_iff.lean](Xenum_isComputableElement_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/isComputableElement_funPresentation_iff.lean](isComputableElement_funPresentation_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_Xenum_iff_map.lean](mem_Xenum_iff_map.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/curry_rel_Xenum_iff.lean](curry_rel_Xenum_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/curry_isComputable.lean](curry_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75.lean](../Theorem75.lean)
