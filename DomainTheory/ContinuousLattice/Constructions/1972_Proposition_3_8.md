# Proposition 3.8

Returning now to $\bar{f}$ we can prove:

**3.8 Proposition.** If $D$ is a continuous lattice and $e : X \rightarrow Y$ a subspace embedding, then for each $f : X \rightarrow D$, the function $\bar{f} : Y \rightarrow D$ given by the formula

$$\bar{f}(y) = \bigsqcup  \sqcap  f(x) : e(x) \in U  : y \in U ,$$

where $U$ ranges over open subsets of $Y$ and $x$ over $X$, is the maximal extension of $f$ to a function in the partially ordered set $[Y \rightarrow D]$.

**Proof:** We are saying that $\bar{f}$ is the maximal solution to the equation

$$f = \bar{f} \circ e.$$

We already know it is a solution, so let $f'$ be any other. We have

$$
\begin{aligned}
f'(y) &= \bigsqcup  \sqcap  f'(z) : z \in U  : y \in U  
&\sqsubseteq \bigsqcup  \sqcap  f'(z) : z \in e(X) \cap U  : y \in U  
&= \bigsqcup  \sqcap  f'(e(x)) : e(x) \in U  : y \in U  
&= \bigsqcup  \sqcap  f(x) : e(x) \in U  : y \in U  
&= \bar{f}(y),
\end{aligned}
$$

which establishes that $f' \sqsubseteq \bar{f}$. $\square$

The reader should not forget that any space (any *given* number of spaces $X$, $Y$, $\ldots$) can be found as a *subspace* of a continuous lattice $D$. Since $D$ is injective any continuous function $f : X \to Y$ can be extended to a continuous function $\bar{f} : D \to D$. Thus the continuous functions from $D$ into $D$ are a rich totality including *all* the structure of continuous functions on *all* the subspaces. And this remark brings us to the study of [function spaces](../FunctionSpaces/1972_Function_spaces.md).

**Subspace.** There is no separate subspace type. A subspace is Mathlib’s `IsEmbedding`. `IsRetractSubspace` requires its section to be an embedding, and this proposition extends a continuous map along an embedding into a continuous lattice by `scottExtend`. The function-space development writes the same formula as `scottSubspaceExtend`.

**Lean 4**

- [ContinuousLattice/Constructions/proposition_3_8.lean](proposition_3_8.lean)
- [ContinuousLattice/Constructions.lean](../Constructions.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf.lean](../FunctionSpaces/scottSubspaceExtendInf.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtend.lean](../FunctionSpaces/scottSubspaceExtend.lean)
- [ContinuousLattice/FunctionSpaces/Basic.lean](../FunctionSpaces/Basic.lean)
- [ContinuousLattice/FunctionSpaces/fix_unique.lean](../FunctionSpaces/fix_unique.lean)
- [ContinuousLattice/FunctionSpaces/image_retr_wayBelow_directed.lean](../FunctionSpaces/image_retr_wayBelow_directed.lean)
- [ContinuousLattice/FunctionSpaces/image_retr_wayBelow_nonempty.lean](../FunctionSpaces/image_retr_wayBelow_nonempty.lean)
- [ContinuousLattice/FunctionSpaces/incl_injective.lean](../FunctionSpaces/incl_injective.lean)
- [ContinuousLattice/FunctionSpaces/incl_preservesDirectedSup.lean](../FunctionSpaces/incl_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/incl_sup.lean](../FunctionSpaces/incl_sup.lean)
- [ContinuousLattice/FunctionSpaces/incl_wayBelow.lean](../FunctionSpaces/incl_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/pointwiseSubbasic_isOpen.lean](../FunctionSpaces/pointwiseSubbasic_isOpen.lean)
- [ContinuousLattice/FunctionSpaces/pointwiseSubbasic_scottOpen.lean](../FunctionSpaces/pointwiseSubbasic_scottOpen.lean)
- [ContinuousLattice/FunctionSpaces/retr_ambientSSup_eq_sSup.lean](../FunctionSpaces/retr_ambientSSup_eq_sSup.lean)
- [ContinuousLattice/FunctionSpaces/retr_bot.lean](../FunctionSpaces/retr_bot.lean)
- [ContinuousLattice/FunctionSpaces/incl_bot.lean](../FunctionSpaces/incl_bot.lean)
- [ContinuousLattice/FunctionSpaces/incl_finset_sup.lean](../FunctionSpaces/incl_finset_sup.lean)
- [ContinuousLattice/FunctionSpaces/incl_sSup.lean](../FunctionSpaces/incl_sSup.lean)
- [ContinuousLattice/FunctionSpaces/retr_eq_sSup.lean](../FunctionSpaces/retr_eq_sSup.lean)
- [ContinuousLattice/FunctionSpaces/retr_wayBelow_of_wayBelow_incl.lean](../FunctionSpaces/retr_wayBelow_of_wayBelow_incl.lean)
- [ContinuousLattice/FunctionSpaces/sInf_image_le_sInf_image_of_subset.lean](../FunctionSpaces/sInf_image_le_sInf_image_of_subset.lean)
- [ContinuousLattice/FunctionSpaces/sSupMaps_apply.lean](../FunctionSpaces/sSupMaps_apply.lean)
- [ContinuousLattice/FunctionSpaces/sSup_image_retr_wayBelow.lean](../FunctionSpaces/sSup_image_retr_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/proposition_2_10_a.lean](../FunctionSpaces/proposition_2_10_a.lean)
- [ContinuousLattice/FunctionSpaces/proposition_2_10_b.lean](../FunctionSpaces/proposition_2_10_b.lean)
- [ContinuousLattice/FunctionSpaces/proposition_2_10.lean](../FunctionSpaces/proposition_2_10.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionSubbasis_isOpen.lean](../FunctionSpaces/scottFunctionSubbasis_isOpen.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionSubbasis_isOpen_scott.lean](../FunctionSpaces/scottFunctionSubbasis_isOpen_scott.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionTopology_eq_induced_pi.lean](../FunctionSpaces/scottFunctionTopology_eq_induced_pi.lean)
- [ContinuousLattice/FunctionSpaces/scottMapPointwiseTopology_eq_induced_pi.lean](../FunctionSpaces/scottMapPointwiseTopology_eq_induced_pi.lean)
- [ContinuousLattice/FunctionSpaces/specializationLe_generateOpen.lean](../FunctionSpaces/specializationLe_generateOpen.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionSpecializationLe.lean](../FunctionSpaces/scottFunctionSpecializationLe.lean)
- [ContinuousLattice/FunctionSpaces/stepMap_apply_of_wayBelow.lean](../FunctionSpaces/stepMap_apply_of_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/stepMap_le_of_wayBelow.lean](../FunctionSpaces/stepMap_le_of_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/stepMap_pointwise_sSup.lean](../FunctionSpaces/stepMap_pointwise_sSup.lean)
- [ContinuousLattice/FunctionSpaces/stepMap_wayBelow.lean](../FunctionSpaces/stepMap_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/wayBelow_finset_sup.lean](../FunctionSpaces/wayBelow_finset_sup.lean)
- [ContinuousLattice/FunctionSpaces/wayBelow_le_finset_sup_step.lean](../FunctionSpaces/wayBelow_le_finset_sup_step.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_2.lean](../FunctionSpaces/proposition_3_2.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3_isContinuousLattice.lean](../FunctionSpaces/theorem_3_3_isContinuousLattice.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3_topology.lean](../FunctionSpaces/theorem_3_3_topology.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3.lean](../FunctionSpaces/theorem_3_3.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3_topology_induced_pi.lean](../FunctionSpaces/theorem_3_3_topology_induced_pi.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4_eval_on_C.lean](../FunctionSpaces/corollary_3_4_eval_on_C.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4.lean](../FunctionSpaces/corollary_3_4.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4_preservesDirectedSup.lean](../FunctionSpaces/corollary_3_4_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4_jointly_continuous.lean](../FunctionSpaces/corollary_3_4_jointly_continuous.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_5_preservesDirectedSup.lean](../FunctionSpaces/proposition_3_5_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_5.lean](../FunctionSpaces/proposition_3_5.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_eq_of_comp.lean](../FunctionSpaces/scottSubspaceExtendInf_eq_of_comp.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_eq_of_ext.lean](../FunctionSpaces/scottSubspaceExtendInf_eq_of_ext.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_le_of_mem.lean](../FunctionSpaces/scottSubspaceExtendInf_le_of_mem.lean)
- [ContinuousLattice/FunctionSpaces/scottMap_eq_sSup_openInfs.lean](../FunctionSpaces/scottMap_eq_sSup_openInfs.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono.lean](../FunctionSpaces/scottSubspaceExtendInf_mono.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono_incl.lean](../FunctionSpaces/scottSubspaceExtendInf_mono_incl.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono_incl_apply.lean](../FunctionSpaces/scottSubspaceExtendInf_mono_incl_apply.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono_retr.lean](../FunctionSpaces/scottSubspaceExtendInf_mono_retr.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtend_eq_of_ext.lean](../FunctionSpaces/scottSubspaceExtend_eq_of_ext.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtend_maximal.lean](../FunctionSpaces/scottSubspaceExtend_maximal.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtend_mono.lean](../FunctionSpaces/scottSubspaceExtend_mono.lean)
