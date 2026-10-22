# Theorem 8.8

**THEOREM 8.8.** The system $\mathcal{U}$ is universal in the sense that, for every countable neighbourhood system $\mathcal{D}$, we have
$$\mathcal{D} \trianglelefteq \mathcal{U}.$$
Moreover, if $\mathcal{D}$ is effectively given, then the projection pair making the embedding can be taken as computable. Indeed there is a correspondence between effectively presented domains and the computable, finitary projections of $\mathcal{U}$.

*Proof:* As $\mathcal{D}$ is countable, we can assume that
$$\mathcal{D} = \{X_n \mid n \in \mathbb{N}\},$$
where $\mathcal{D}$ is a system over a set $\Delta$ (say, $X_0 = \Delta$). We shall do the effective and general cases together, where for the latter all remarks on recursiveness are just left out. So, if we want $\mathcal{D}$ effectively given, the above enumeration should be taken as the computable presentation.

Without loss of generality we can assume $\mathcal{D} \cong \mathcal{D}^\dagger$, since otherwise we would just replace $\mathcal{D}$ by $\mathcal{D}^\dagger$. The advantage of this preparation is that unions in $\mathcal{D}^\dagger$ keep things rather *separate* (as we noticed in constructing $\mathbb{P}\mathcal{D}$). In particular, we can be sure of this equivalence:

$$(\blacklozenge) \qquad X_m \subseteq \bigcup_{i < k} X_{n_i} \quad \text{iff} \quad \exists i < k.\ X_m \subseteq X_{n_i}.$$

This property, for example, fails for the system $\mathcal{U}$ as presented in Definition 8.7. However, that observation is of no moment, because we are employing the assumption with respect to $\mathcal{D}$ not $\mathcal{U}$.

The reason for the assumption is this: for $\delta \in \{+, -\}$ define for $X \in \mathcal{D}$:

$$
\begin{aligned}
\delta X &= X && \text{if } \delta = + ; \\
&= \Delta \setminus X && \text{if } \delta = - .
\end{aligned}
$$

(A similar notation will be used for $Y \in \mathcal{U}$.) Then for $\delta \in \{+, -\}^n$ the sets of the form

$$\bigcap_{i < n} \delta_i X_i \quad (= X_\delta, \text{ for short})$$

form a partition of $\Delta$ into (at most) $2^n$ parts. The reason for assumption $(\blacklozenge)$ is that we can effectively decide for each $\delta \in \{+, -\}^n$ whether one of these intersections is empty or not. (Why? — assuming that $\mathcal{D}$ is effectively given, of course). If for some reason we had not wanted to pass to $\mathcal{D}^\dagger$, we could have made this stronger assumption of decidability on the (positive) system $\mathcal{D}$. ($\mathcal{U}$, for example, satisfies it.)

Suppose, corresponding to $X_0, X_1, \ldots, X_{n-1}$, we have selected $Y_0, Y_1, \ldots, Y_{n-1} \in \mathcal{U}$ so that, for all $\delta \in \{+, -\}^n$,

$$(\blacksquare) \qquad \bigcap_{i < n} \delta_i X_i = \emptyset \quad \text{iff} \quad \bigcap_{i < n} \delta_i Y_i = \emptyset.$$
We wish to show - effectively - how to choose $Y_n$ corresponding to $X_n$, so that $(\blacksquare)$ holds with $n+1$ replacing $n$. Proceeding inductively, we obtain a recursive enumeration of sets $Y_n \in \mathcal{U}$ so that

$$\mathcal{D} \equiv \{ Y_n \mid n \in \mathbb{N} \} \triangleleft \mathcal{U} .$$

Clearly the isomorphism (matching $X_i$ to $Y_i$) will be computable and the projection is computable. (It will then remain only to consider the arbitrary finitary computable projection to complete the proof of the theorem.)

So, consider $X_n$; for each $\delta \in \{+, -\}^n$ there are four cases:

$$
\begin{aligned}
X_\delta \cap X_n &= \emptyset, & X_\delta \cap -X_n &= \emptyset, \\
X_\delta \cap X_n &\neq \emptyset, & X_\delta \cap -X_n &\neq \emptyset .
\end{aligned}
$$

Corresponding to $X_\delta$ is a similar intersection $Y_\delta$. If $X_\delta$ were $\emptyset$, then $Y_\delta$ would be also. If not, $Y_\delta \subseteq [0, 1)$ is a union of rational intervals that can be written down explicitly. (Why?) In our four cases on $X_n$, the first implies the fourth. (Why?) Thus, we need only make some choices in these circumstances:

$$
\begin{aligned}
X_\delta \cap X_n = \emptyset &: \text{choose } I_{\delta, n} = \emptyset ; \\
X_\delta \cap -X_n = \emptyset &: \text{choose } I_{\delta, n} = Y_\delta ; \\
\text{otherwise} &: \text{choose } I_{\delta, n} \subseteq Y_\delta, \text{ with } \emptyset \neq I_{\delta, n} \neq Y_\delta .
\end{aligned}
$$

All these cases are decidable by assumption on $\mathcal{D}$, and the effective choice of (unions of) intervals is effective by construction of $\mathcal{U}$. Now set

$$Y_n = \bigcup_{\delta \in \{+, -\}^n} I_{\delta, n} \neq \emptyset .$$

The set $Y_n \in \mathcal{U}$, it can be found effectively, and $(\blacksquare)$ is obviously satisfied for $n+1$ .

Finally, suppose that $a$ is a computable, finitary projection of $\mathcal{U}$. As we have seen in the proof of 8.5, the domain corresponding to the range of $a$ is isomorphic to the neighbourhood system

$$\{ Y \in \mathcal{U} \mid Y \ a \ Y \} \triangleleft \mathcal{U} .$$
Clearly, if $a$ as a set of ordered pairs of neighbourhoods is recursively enumerable, then the above set is also recursively enumerable (because equality between neighbourhoods is decidable). It follows easily that the subsystem is effectively given as a neighbourhood system in its own right. $\square$

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/SplitSpec.lean](Theorem88/SplitSpec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/exists_split.lean](Theorem88/exists_split.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/genAtom.lean](Theorem88/genAtom.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/atomU.lean](Theorem88/atomU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/atomU_zero.lean](Theorem88/atomU_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/extendTrue.lean](Theorem88/extendTrue.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/Yseq.lean](Theorem88/Yseq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/restrictFin.lean](Theorem88/restrictFin.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/splitChoice.lean](Theorem88/splitChoice.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/Basic.lean](Theorem88/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/splitChoice_isSplitSpec.lean](Theorem88/splitChoice_isSplitSpec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet.lean](Theorem88a/idxSet.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/mem_idxSet.lean](Theorem88a/mem_idxSet.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/D_mem_e.lean](Theorem88a/D_mem_e.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx.lean](Theorem88a/Yidx.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/e_subset_master.lean](Theorem88a/e_subset_master.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_inter_of_inter_eq.lean](Theorem88a/idxSet_inter_of_inter_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_zero_eq_univ.lean](Theorem88a/idxSet_zero_eq_univ.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_zero.lean](Theorem88a/idxSet_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/self_mem_idxSet.lean](Theorem88a/self_mem_idxSet.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_subset_iff.lean](Theorem88a/idxSet_subset_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/univ_nonempty_nat.lean](Theorem88a/univ_nonempty_nat.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_empty_or_mem.lean](Theorem88a/Yidx_empty_or_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_nonempty.lean](Theorem88a/Yidx_nonempty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_mem.lean](Theorem88a/Yidx_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_subset_master.lean](Theorem88a/Yidx_subset_master.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_zero.lean](Theorem88a/Yidx_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/embed_subset_iff.lean](Theorem88a/embed_subset_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/embed_eq_iff.lean](Theorem88a/embed_eq_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/exists_inter_index_of_dmem.lean](Theorem88a/exists_inter_index_of_dmem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/DprimeU.lean](Theorem88a/DprimeU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/exists_inter_index_of_nonempty.lean](Theorem88a/exists_inter_index_of_nonempty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/DprimeU_subsystem.lean](Theorem88a/DprimeU_subsystem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/toD.lean](Theorem88a/toD.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/toDprimeU.lean](Theorem88a/toDprimeU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/domainIso.lean](Theorem88a/domainIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Basic.lean](Theorem88a/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_eq_iff.lean](Theorem88a/idxSet_eq_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_nonempty.lean](Theorem88a/idxSet_nonempty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/isomorphic_DprimeU.lean](Theorem88a/isomorphic_DprimeU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/theorem_8_8_a.lean](Theorem88a/theorem_8_8_a.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/theorem_8_8.lean](Theorem88a/theorem_8_8.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/IPos.lean](DAtomDecidable/IPos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/IPos_cons.lean](DAtomDecidable/IPos_cons.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/IPos_nil.lean](DAtomDecidable/IPos_nil.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/DAtom.lean](DAtomDecidable/DAtom.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/idxSet_masterIdx_eq_univ.lean](DAtomDecidable/idxSet_masterIdx_eq_univ.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetFoldCode_eq.lean](DAtomDecidable/meetFoldCode_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetFold_cons.lean](DAtomDecidable/meetFold_cons.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetStep.lean](DAtomDecidable/meetStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetFold.lean](DAtomDecidable/meetFold.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetFold_nil.lean](DAtomDecidable/meetFold_nil.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetStepCode.lean](DAtomDecidable/meetStepCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetFoldCode.lean](DAtomDecidable/meetFoldCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/DAtomEmptyChar.lean](DAtomDecidable/DAtomEmptyChar.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/Basic.lean](DAtomDecidable/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetStep_ok_le_one.lean](DAtomDecidable/meetStep_ok_le_one.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetStep_spec.lean](DAtomDecidable/meetStep_spec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetFold_foldl_spec.lean](DAtomDecidable/meetFold_foldl_spec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/meetFold_spec.lean](DAtomDecidable/meetFold_spec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/mem_IPos.lean](DAtomDecidable/mem_IPos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/mem_DAtom.lean](DAtomDecidable/mem_DAtom.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/DAtom_eq_empty_iff.lean](DAtomDecidable/DAtom_eq_empty_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/DAtomEmptyChar_eq_one_iff.lean](DAtomDecidable/DAtomEmptyChar_eq_one_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/primrec_meetStepCode.lean](DAtomDecidable/primrec_meetStepCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/primrec_meetFoldCode.lean](DAtomDecidable/primrec_meetFoldCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/primrec_DAtomEmptyChar.lean](DAtomDecidable/primrec_DAtomEmptyChar.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable/DAtom_recDecidable.lean](DAtomDecidable/DAtom_recDecidable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/DAtomDecidable.lean](DAtomDecidable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx.lean](Theorem88b/eIdx.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx_involutive.lean](Theorem88b/eIdx_involutive.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx_primrec.lean](Theorem88b/eIdx_primrec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/P0.lean](Theorem88b/P0.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/P0_X.lean](Theorem88b/P0_X.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/posnegList.lean](Theorem88b/posnegList.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/Basic.lean](Theorem88b/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx_zero.lean](Theorem88b/eIdx_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/genAtom_empty_iff.lean](Theorem88b/genAtom_empty_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/hcover.lean](Theorem88b/hcover.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/he0.lean](Theorem88b/he0.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_cons_computable.lean](Theorem88c/DprimeU_cons_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_inter_spec.lean](Theorem88c/DprimeU_inter_spec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_isEffectivelyGiven.lean](Theorem88c/DprimeU_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capNegCode.lean](Theorem88c/capNegCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capNegCode_eq.lean](Theorem88c/capNegCode_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capPosCode.lean](Theorem88c/capPosCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capPosCode_eq.lean](Theorem88c/capPosCode_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/idxSet_inter_eq_iff_DAtom.lean](Theorem88c/idxSet_inter_eq_iff_DAtom.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/inclK_i_recDecidable.lean](Theorem88c/inclK_i_recDecidable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/inclK_j_recDecidable.lean](Theorem88c/inclK_j_recDecidable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/primrec_capNegCode.lean](Theorem88c/primrec_capNegCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/primrec_capPosCode.lean](Theorem88c/primrec_capPosCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DAtom_pair_recDecidable.lean](Theorem88c/DAtom_pair_recDecidable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_interEq_computable.lean](Theorem88c/DprimeU_interEq_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeUPresentation.lean](Theorem88c/DprimeUPresentation.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/Basic.lean](Theorem88c/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/packState.lean](Theorem88d/packState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateCode.lean](Theorem88d/stateCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateNeg.lean](Theorem88d/stateNeg.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/statePos.lean](Theorem88d/statePos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateRem.lean](Theorem88d/stateRem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateRem_packState.lean](Theorem88d/stateRem_packState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/statePos_packState.lean](Theorem88d/statePos_packState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateNeg_packState.lean](Theorem88d/stateNeg_packState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateCode_packState.lean](Theorem88d/stateCode_packState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomBase.lean](Theorem88d/atomBase.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/datomDec.lean](Theorem88d/datomDec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/deltaOf.lean](Theorem88d/deltaOf.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/encodeBits.lean](Theorem88d/encodeBits.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/unionUX.lean](Theorem88d/unionUX.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/wState.lean](Theorem88d/wState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/wY.lean](Theorem88d/wY.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomStep.lean](Theorem88d/atomStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCodeState.lean](Theorem88d/atomUCodeState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode.lean](Theorem88d/atomUCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUNeg.lean](Theorem88d/atomUNeg.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUPos.lean](Theorem88d/atomUPos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUEmpty.lean](Theorem88d/atomUEmpty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFoldStep.lean](Theorem88d/yFoldStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold.lean](Theorem88d/yFold.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/YseqCode.lean](Theorem88d/YseqCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/Yc.lean](Theorem88d/Yc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/Basic.lean](Theorem88d/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/DAtom_union.lean](Theorem88d/DAtom_union.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/U_mem_union_UX.lean](Theorem88d/U_mem_union_UX.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_mem.lean](Theorem88d/atomUCode_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUEmpty_congr.lean](Theorem88d/atomUEmpty_congr.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUEmpty_zero_or_one.lean](Theorem88d/atomUEmpty_zero_or_one.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/datomDec_eq_zero.lean](Theorem88d/datomDec_eq_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/deltaOf_mod_two_pow_of_lt.lean](Theorem88d/deltaOf_mod_two_pow_of_lt.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCodeState_congr_twin.lean](Theorem88d/atomUCodeState_congr_twin.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/eq_of_deltaOf_agree_of_lt_two_pow.lean](Theorem88d/eq_of_deltaOf_agree_of_lt_two_pow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/mem_decodeQPairList_appendCode.lean](Theorem88d/mem_decodeQPairList_appendCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/presentedIntervals_decodeQPairList_appendCode.lean](Theorem88d/presentedIntervals_decodeQPairList_appendCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/UX_unionUX.lean](Theorem88d/UX_unionUX.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomBase.lean](Theorem88d/primrec_atomBase.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_datomDec.lean](Theorem88d/primrec_datomDec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_stateCode.lean](Theorem88d/primrec_stateCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_stateNeg.lean](Theorem88d/primrec_stateNeg.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_statePos.lean](Theorem88d/primrec_statePos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_stateRem.lean](Theorem88d/primrec_stateRem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_unionUX.lean](Theorem88d/primrec_unionUX.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_wState.lean](Theorem88d/primrec_wState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_wY.lean](Theorem88d/primrec_wY.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomStep.lean](Theorem88d/primrec_atomStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUCodeState.lean](Theorem88d/primrec_atomUCodeState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUCode.lean](Theorem88d/primrec_atomUCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUNeg.lean](Theorem88d/primrec_atomUNeg.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUPos.lean](Theorem88d/primrec_atomUPos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUEmpty.lean](Theorem88d/primrec_atomUEmpty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_yFoldStep.lean](Theorem88d/primrec_yFoldStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_yFold.lean](Theorem88d/primrec_yFold.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_YseqCode.lean](Theorem88d/primrec_YseqCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFoldStep_eq.lean](Theorem88d/yFoldStep_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_succ.lean](Theorem88d/yFold_succ.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_zero.lean](Theorem88d/yFold_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_found_le_one.lean](Theorem88d/yFold_found_le_one.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_found_iff.lean](Theorem88d/yFold_found_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_mem_iff.lean](Theorem88d/yFold_mem_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_two_pow_found.lean](Theorem88d/yFold_two_pow_found.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/mem_UX_YseqCode_iff.lean](Theorem88d/mem_UX_YseqCode_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_disjoint_YseqCode_of_posTwin_empty.lean](Theorem88d/atomUCode_disjoint_YseqCode_of_posTwin_empty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_succ_true.lean](Theorem88d/atomUCode_succ_true.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_inter_succ_empty_of_junk.lean](Theorem88d/atomUCode_inter_succ_empty_of_junk.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_succ_false.lean](Theorem88d/atomUCode_succ_false.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_eq_genAtomYseqCode.lean](Theorem88d/atomUCode_eq_genAtomYseqCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/genAtom_Yc_empty_iff.lean](Theorem88d/genAtom_Yc_empty_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_isEffectivelyGiven.lean](Theorem88e/DprimeUCode_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/Yc_subset_master.lean](Theorem88e/Yc_subset_master.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/Yc_zero_eq_master.lean](Theorem88e/Yc_zero_eq_master.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/encodeBits.lean](Theorem88e/encodeBits.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/encodeBits_lt.lean](Theorem88e/encodeBits_lt.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/deltaOf_encodeBits.lean](Theorem88e/deltaOf_encodeBits.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/hcoreIdxYc.lean](Theorem88e/hcoreIdxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/inclK_i_recDecidable_code.lean](Theorem88e/inclK_i_recDecidable_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/inclK_j_recDecidable_code.lean](Theorem88e/inclK_j_recDecidable_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/isomorphic_DprimeUCode.lean](Theorem88e/isomorphic_DprimeUCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_dir_idxYc.lean](Theorem88e/transfer_dir_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_empty_iff_idxYc.lean](Theorem88e/transfer_empty_iff_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_double_subset_iff_idxYc.lean](Theorem88e/transfer_double_subset_iff_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_inter_empty_iff_idxYc.lean](Theorem88e/transfer_inter_empty_iff_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_subset_iff_idxYc.lean](Theorem88e/transfer_subset_iff_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_subset_iff_code.lean](Theorem88e/embed_subset_iff_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_eq_iff_code.lean](Theorem88e/embed_eq_iff_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_eq_iff_raw_code.lean](Theorem88e/embed_eq_iff_raw_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_subset_iff_raw_code.lean](Theorem88e/embed_subset_iff_raw_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_cons_computable.lean](Theorem88e/DprimeUCode_cons_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_inter_eq_iff_idxYc.lean](Theorem88e/transfer_inter_eq_iff_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_interEq_computable.lean](Theorem88e/DprimeUCode_interEq_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_inter_spec.lean](Theorem88e/DprimeUCode_inter_spec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/exists_inter_index_of_dmem_code.lean](Theorem88e/exists_inter_index_of_dmem_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode.lean](Theorem88e/DprimeUCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCodePresentation.lean](Theorem88e/DprimeUCodePresentation.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/exists_inter_index_of_nonempty_code.lean](Theorem88e/exists_inter_index_of_nonempty_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_subsystem.lean](Theorem88e/DprimeUCode_subsystem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/toDCode.lean](Theorem88e/toDCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/toDprimeUCode.lean](Theorem88e/toDprimeUCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/domainIsoCode.lean](Theorem88e/domainIsoCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/Basic.lean](Theorem88e/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/Basic.lean](Theorem88f/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/DprimeUCode_inj_isComputableMap.lean](Theorem88f/DprimeUCode_inj_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/DprimeUCode_proj_isComputableMap.lean](Theorem88f/DprimeUCode_proj_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/DprimeUCode_projectionPair_isComputable.lean](Theorem88f/DprimeUCode_projectionPair_isComputable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88g/Basic.lean](Theorem88g/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88g/theorem_8_8_b.lean](Theorem88g/theorem_8_8_b.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/DiagFixed.lean](Theorem88h/DiagFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/Basic.lean](Theorem88h/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/diagFixed_iff_fixedNbhd_mem.lean](Theorem88h/diagFixed_iff_fixedNbhd_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/diagFixed_isREPred.lean](Theorem88h/diagFixed_isREPred.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/diagFixed_exists_qChar.lean](Theorem88h/diagFixed_exists_qChar.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/diagFixed_masterIdx.lean](Theorem88i/diagFixed_masterIdx.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFoldCode_eq.lean](Theorem88i/myFoldCode_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_cons.lean](Theorem88i/myFold_cons.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myStep.lean](Theorem88i/myStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold.lean](Theorem88i/myFold.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_nil.lean](Theorem88i/myFold_nil.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myStepCode.lean](Theorem88i/myStepCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFoldCode.lean](Theorem88i/myFoldCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/Basic.lean](Theorem88i/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myStep_diagFixed_of_diagFixed.lean](Theorem88i/myStep_diagFixed_of_diagFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_diagFixed_of_diagFixed.lean](Theorem88i/myFold_diagFixed_of_diagFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_diagFixed.lean](Theorem88i/myFold_diagFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/diagFixed_myFoldCode.lean](Theorem88i/diagFixed_myFoldCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/primrec_myStepCode.lean](Theorem88i/primrec_myStepCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/primrec_myFoldCode.lean](Theorem88i/primrec_myFoldCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X.lean](Theorem88j/D_X.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/Basic.lean](Theorem88j/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X_mem.lean](Theorem88j/D_X_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X_of_diagFixed.lean](Theorem88j/D_X_of_diagFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X_surj.lean](Theorem88j/D_X_surj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/Basic.lean](Theorem88k/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/D_X_cons_iff.lean](Theorem88k/D_X_cons_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/D_X_cons_computable.lean](Theorem88k/D_X_cons_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/D_X_interEq_computable.lean](Theorem88k/D_X_interEq_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_X_inter_eq.lean](Theorem88l/D_X_inter_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_inter.lean](Theorem88l/D_inter.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/Basic.lean](Theorem88l/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_inter_primrec.lean](Theorem88l/D_inter_primrec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/myStep_subset.lean](Theorem88l/myStep_subset.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/myFoldl_subset.lean](Theorem88l/myFoldl_subset.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/myFoldl_inter_of_le.lean](Theorem88l/myFoldl_inter_of_le.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_X_inter_spec.lean](Theorem88l/D_X_inter_spec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88m/Basic.lean](Theorem88m/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88m/fixedNbhd_isEffectivelyGiven.lean](Theorem88m/fixedNbhd_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88m/theorem_8_8_c.lean](Theorem88m/theorem_8_8_c.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88.lean](Theorem88.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/PalomarExamples/Basic.lean](PalomarExamples/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/PalomarExamples/P4_embeds.lean](PalomarExamples/P4_embeds.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/PalomarExamples/Ssys_embeds.lean](PalomarExamples/Ssys_embeds.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/PalomarExamples.lean](PalomarExamples.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj.lean](Theorem88n/isoInj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj_comp_isoProj.lean](Theorem88n/isoInj_comp_isoProj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj_rel_iff_incl.lean](Theorem88n/isoInj_rel_iff_incl.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj_isComputableMap.lean](Theorem88n/isoInj_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj.lean](Theorem88n/isoProj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/Basic.lean](Theorem88n/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj_comp_isoInj.lean](Theorem88n/isoProj_comp_isoInj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj_rel_iff_incl.lean](Theorem88n/isoProj_rel_iff_incl.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj_isComputableMap.lean](Theorem88n/isoProj_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/theorem_8_8_b_strong.lean](Theorem88n/theorem_8_8_b_strong.lean)
