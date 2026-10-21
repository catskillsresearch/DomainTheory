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

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_inter_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_inter_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_isComputableElement_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_isComputableElement_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_neg.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_neg.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_pos.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_pos.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_singleton.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_singleton.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/andFoldl_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/andFoldl_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/andFoldl_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/andFoldl_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStp_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/bitSelect.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/bitSelect.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/bitSelect_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/bitSelect_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/botMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/botMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/botMap_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/botMap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condFoldl_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condFoldl_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_cons_neg.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_cons_neg.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_cons_pos.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_cons_pos.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_eq_interYs.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_eq_interYs.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_subset.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_subset.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consChain_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consChain_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consCharAt.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consCharAt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consPairChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consPairChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consPairChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consPairChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consUpd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consUpd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/curry_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/curry_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/curry_rel_Xenum_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/curry_rel_Xenum_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_appendCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_appendStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_appendStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_encodeList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_encodeList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_foldl_appendStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_foldl_appendStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/eqEnumChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/eqEnumChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/eqEnumChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/eqEnumChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/evalMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/evalMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/evalMap_rel_prodNbhd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/evalMap_rel_prodNbhd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/exists_funListOf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/exists_funListOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funConsChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funConsChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funImpChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funImpChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_append.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_append.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_valid.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_valid.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair_fst.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair_fst.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair_snd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair_snd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/idxchain.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/idxchain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interEqChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interEqChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interFrom.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interFrom.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList_subset_base.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList_subset_base.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsIdx_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsIdx_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYs_funList_mem_of_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYs_funList_mem_of_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/isComputableElement_funPresentation_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/isComputableElement_funPresentation_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_Xenum_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_Xenum_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_Xenum_iff_map.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_Xenum_iff_map.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_condSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_condSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_appendCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_consPairChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_consPairChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_eqEnumChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_eqEnumChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interYsIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interYsIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interYsStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interYsStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_subChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_subChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_subStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_subStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_trivStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_trivStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_trivialChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_trivialChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/rel_interYs_funList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/rel_interYs_funList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/selectFn_isOne.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/selectFn_isOne.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/selectFn_mul_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/selectFn_mul_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_appendCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_eq_univ_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_eq_univ_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivialChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivialChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivialChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivialChar_spec.lean)
