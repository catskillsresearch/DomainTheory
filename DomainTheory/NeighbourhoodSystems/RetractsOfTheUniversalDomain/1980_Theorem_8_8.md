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

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/SplitSpec.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/SplitSpec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/Yseq.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/Yseq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/atomU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/atomU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/atomU_zero.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/atomU_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/exists_split.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/exists_split.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/extendTrue.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/extendTrue.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/genAtom.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/genAtom.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/restrictFin.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/restrictFin.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/splitChoice.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/splitChoice.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/splitChoice_isSplitSpec.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88/splitChoice_isSplitSpec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/D_mem_e.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/D_mem_e.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/DprimeU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/DprimeU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/DprimeU_subsystem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/DprimeU_subsystem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_empty_or_mem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_empty_or_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_mem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_nonempty.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_nonempty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_subset_master.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_subset_master.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_zero.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/Yidx_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/domainIso.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/domainIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/e_subset_master.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/e_subset_master.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/embed_eq_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/embed_eq_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/embed_subset_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/embed_subset_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/exists_inter_index_of_dmem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/exists_inter_index_of_dmem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/exists_inter_index_of_nonempty.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/exists_inter_index_of_nonempty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_eq_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_eq_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_inter_of_inter_eq.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_inter_of_inter_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_nonempty.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_nonempty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_subset_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_subset_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_zero.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_zero_eq_univ.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/idxSet_zero_eq_univ.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/isomorphic_DprimeU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/isomorphic_DprimeU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/mem_idxSet.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/mem_idxSet.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/self_mem_idxSet.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/self_mem_idxSet.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/theorem_8_8.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/theorem_8_8.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/theorem_8_8_a.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/theorem_8_8_a.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/toD.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/toD.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/toDprimeU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/toDprimeU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/univ_nonempty_nat.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88a/univ_nonempty_nat.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/P0.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/P0.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/P0_X.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/P0_X.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx_involutive.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx_involutive.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx_primrec.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx_primrec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx_zero.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/eIdx_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/genAtom_empty_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/genAtom_empty_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/hcover.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/hcover.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/he0.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/he0.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/posnegList.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88b/posnegList.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DAtom_pair_recDecidable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DAtom_pair_recDecidable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeUPresentation.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeUPresentation.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_cons_computable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_cons_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_interEq_computable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_interEq_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_inter_spec.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_inter_spec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/DprimeU_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capNegCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capNegCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capNegCode_eq.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capNegCode_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capPosCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capPosCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capPosCode_eq.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/capPosCode_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/idxSet_inter_eq_iff_DAtom.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/idxSet_inter_eq_iff_DAtom.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/inclK_i_recDecidable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/inclK_i_recDecidable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/inclK_j_recDecidable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/inclK_j_recDecidable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/primrec_capNegCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/primrec_capNegCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/primrec_capPosCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88c/primrec_capPosCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/DAtom_union.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/DAtom_union.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/UX_unionUX.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/UX_unionUX.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/U_mem_union_UX.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/U_mem_union_UX.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/Yc.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/Yc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/YseqCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/YseqCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomBase.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomBase.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomStep.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCodeState.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCodeState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCodeState_congr_twin.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCodeState_congr_twin.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_disjoint_YseqCode_of_posTwin_empty.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_disjoint_YseqCode_of_posTwin_empty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_eq_genAtomYseqCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_eq_genAtomYseqCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_inter_succ_empty_of_junk.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_inter_succ_empty_of_junk.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_mem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_succ_false.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_succ_false.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_succ_true.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUCode_succ_true.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUEmpty.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUEmpty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUEmpty_congr.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUEmpty_congr.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUEmpty_zero_or_one.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUEmpty_zero_or_one.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUNeg.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUNeg.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUPos.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/atomUPos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/datomDec.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/datomDec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/datomDec_eq_zero.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/datomDec_eq_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/deltaOf.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/deltaOf.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/deltaOf_mod_two_pow_of_lt.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/deltaOf_mod_two_pow_of_lt.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/encodeBits.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/encodeBits.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/eq_of_deltaOf_agree_of_lt_two_pow.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/eq_of_deltaOf_agree_of_lt_two_pow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/genAtom_Yc_empty_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/genAtom_Yc_empty_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/mem_UX_YseqCode_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/mem_UX_YseqCode_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/mem_decodeQPairList_appendCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/mem_decodeQPairList_appendCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/packState.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/packState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/presentedIntervals_decodeQPairList_appendCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/presentedIntervals_decodeQPairList_appendCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_YseqCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_YseqCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomBase.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomBase.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomStep.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUCodeState.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUCodeState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUEmpty.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUEmpty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUNeg.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUNeg.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUPos.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_atomUPos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_datomDec.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_datomDec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_stateCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_stateCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_stateNeg.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_stateNeg.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_statePos.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_statePos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_stateRem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_stateRem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_unionUX.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_unionUX.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_wState.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_wState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_wY.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_wY.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_yFold.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_yFold.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_yFoldStep.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/primrec_yFoldStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateCode_packState.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateCode_packState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateNeg.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateNeg.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateNeg_packState.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateNeg_packState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/statePos.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/statePos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/statePos_packState.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/statePos_packState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateRem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateRem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateRem_packState.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/stateRem_packState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/unionUX.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/unionUX.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/wState.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/wState.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/wY.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/wY.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFoldStep.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFoldStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFoldStep_eq.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFoldStep_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_found_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_found_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_found_le_one.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_found_le_one.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_mem_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_mem_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_succ.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_succ.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_two_pow_found.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_two_pow_found.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_zero.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88d/yFold_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCodePresentation.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCodePresentation.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_cons_computable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_cons_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_interEq_computable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_interEq_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_inter_spec.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_inter_spec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_subsystem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/DprimeUCode_subsystem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/Yc_subset_master.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/Yc_subset_master.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/Yc_zero_eq_master.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/Yc_zero_eq_master.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/deltaOf_encodeBits.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/deltaOf_encodeBits.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/domainIsoCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/domainIsoCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_eq_iff_code.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_eq_iff_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_eq_iff_raw_code.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_eq_iff_raw_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_subset_iff_code.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_subset_iff_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_subset_iff_raw_code.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/embed_subset_iff_raw_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/encodeBits.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/encodeBits.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/encodeBits_lt.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/encodeBits_lt.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/exists_inter_index_of_dmem_code.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/exists_inter_index_of_dmem_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/exists_inter_index_of_nonempty_code.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/exists_inter_index_of_nonempty_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/hcoreIdxYc.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/hcoreIdxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/inclK_i_recDecidable_code.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/inclK_i_recDecidable_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/inclK_j_recDecidable_code.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/inclK_j_recDecidable_code.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/isomorphic_DprimeUCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/isomorphic_DprimeUCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/toDCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/toDCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/toDprimeUCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/toDprimeUCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_dir_idxYc.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_dir_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_double_subset_iff_idxYc.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_double_subset_iff_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_empty_iff_idxYc.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_empty_iff_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_inter_empty_iff_idxYc.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_inter_empty_iff_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_inter_eq_iff_idxYc.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_inter_eq_iff_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_subset_iff_idxYc.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88e/transfer_subset_iff_idxYc.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/DprimeUCode_inj_isComputableMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/DprimeUCode_inj_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/DprimeUCode_proj_isComputableMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/DprimeUCode_proj_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/DprimeUCode_projectionPair_isComputable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88f/DprimeUCode_projectionPair_isComputable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88g/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88g/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88g/theorem_8_8_b.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88g/theorem_8_8_b.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/DiagFixed.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/DiagFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/diagFixed_exists_qChar.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/diagFixed_exists_qChar.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/diagFixed_iff_fixedNbhd_mem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/diagFixed_iff_fixedNbhd_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/diagFixed_isREPred.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88h/diagFixed_isREPred.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/diagFixed_masterIdx.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/diagFixed_masterIdx.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/diagFixed_myFoldCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/diagFixed_myFoldCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFoldCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFoldCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFoldCode_eq.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFoldCode_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_cons.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_cons.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_diagFixed.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_diagFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_diagFixed_of_diagFixed.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_diagFixed_of_diagFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_nil.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myFold_nil.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myStep.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myStep.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myStepCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myStepCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myStep_diagFixed_of_diagFixed.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/myStep_diagFixed_of_diagFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/primrec_myFoldCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/primrec_myFoldCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/primrec_myStepCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88i/primrec_myStepCode.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X_mem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X_of_diagFixed.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X_of_diagFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X_surj.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88j/D_X_surj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/D_X_cons_computable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/D_X_cons_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/D_X_cons_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/D_X_cons_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/D_X_interEq_computable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88k/D_X_interEq_computable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_X_inter_eq.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_X_inter_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_X_inter_spec.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_X_inter_spec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_inter.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_inter.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_inter_primrec.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/D_inter_primrec.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/myFoldl_inter_of_le.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/myFoldl_inter_of_le.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/myFoldl_subset.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/myFoldl_subset.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/myStep_subset.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88l/myStep_subset.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88m/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88m/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88m/fixedNbhd_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88m/fixedNbhd_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88m/theorem_8_8_c.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88m/theorem_8_8_c.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj_comp_isoProj.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj_comp_isoProj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj_isComputableMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj_rel_iff_incl.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoInj_rel_iff_incl.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj_comp_isoInj.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj_comp_isoInj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj_isComputableMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj_rel_iff_incl.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/isoProj_rel_iff_incl.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/theorem_8_8_b_strong.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem88n/theorem_8_8_b_strong.lean)
