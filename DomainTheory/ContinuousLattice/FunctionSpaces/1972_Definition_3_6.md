# Definition 3.6

We need not enumerate the many corollaries that follow easily now from this result. We mention, however, that composition $f \circ g$ of functions (on continuous lattices) is continuous in the two function variables, where we write

$$
(f \circ g)(x) = f(g(x)).
$$

What will be useful will be to return at this point to a discussion of the injective properties of continuous lattices. If one continuous lattice is a subspace of another it is of course a retract. This relationship between spaces can be given by a pair of continuous maps

$$i : D \to D' \quad \text{and} \quad j : D' \to D,$$

where

$$j \circ i = \text{id}_D = \lambda x : D . x.$$

The composition $i \circ j : D' \to i(D)$ is the retraction onto the subspace corresponding to $D$ under $i$. Now if we have a diagram:

$$
\begin{gathered}
D \xrightarrow[\ j\ ]{i} D' 
f \searrow \qquad \swarrow \tilde{f} = f \circ j 
D''
\end{gathered}
$$

the given continuous $f$ is at once extendable from $D$ to $D'$ by the obvious definition of $\tilde{f}$. This $\tilde{f}$ is not the $\bar{f}$ used in the proof of 2.11, and it will be well to sort out the connections. On one side note that if $f'$ is any function which extends $f$, then we have $f = f' \circ i$. But this implies

$$\tilde{f} = f \circ j = f' \circ i \circ j,$$

which shows that $\tilde{f}$ is a "degraded" version of $f'$. There is one situation where this type of degrading is especially nice.

**3.6 Definition.** A continuous lattice $D$ is said to be a *projection* of a continuous lattice $D'$ iff there are a pair of continuous maps

$$i : D \to D' \quad \text{and} \quad j : D' \to D$$

such that not only

$$j \circ i = \text{id}_D,$$

but also

$$i \circ j \sqsubseteq \text{id}_{D'}.$$

Thus, in case our retraction is a projection, we have $\tilde{f} \sqsubseteq f'$, which means that $\tilde{f}$ is the *minimal* extension of $f \in [D \to D'']$ to a function in $[D' \to D'']$. We will discuss the nature of $\tilde{f}$ in a moment. But before we do we pause to remark that the correspondence $f \rightsquigarrow \tilde{f}$ is *continuous*, and this fact is easily extended.

**Retract.** `IsContinuousLatticeRetraction` and `IsContinuousLatticeProjection` are this definition: Scott maps $i$ and $j$ with $j \circ i = \mathrm{id}$, and, for a projection, also $i \circ j \sqsubseteq \mathrm{id}$. The function-space and inverse-limit proofs are built on them. The subspace retract used for injective spaces is [Proposition 1.4](../Injective/1972_Proposition_1_4.md), and the idempotent representation on a power of $\mathbb{O}$ is [Theorem 2.12](../Theorem212/1972_Theorem_2_12.md).

**Lean 4**

- [ContinuousLattice/FunctionSpaces/IsContinuousLatticeRetraction.lean](IsContinuousLatticeRetraction.lean)
- [ContinuousLattice/FunctionSpaces/ScottMapRetraction.lean](ScottMapRetraction.lean)
- [ContinuousLattice/FunctionSpaces/IsContinuousLatticeProjection.lean](IsContinuousLatticeProjection.lean)
- [ContinuousLattice/FunctionSpaces/ScottMapProjection.lean](ScottMapProjection.lean)
- [ContinuousLattice/FunctionSpaces/const.lean](const.lean)
- [ContinuousLattice/FunctionSpaces/bot.lean](bot.lean)
- [ContinuousLattice/FunctionSpaces/continuousMapInducedPiTopology.lean](continuousMapInducedPiTopology.lean)
- [ContinuousLattice/FunctionSpaces/le.lean](le.lean)
- [ContinuousLattice/FunctionSpaces/le_antisymm'.lean](le_antisymm'.lean)
- [ContinuousLattice/FunctionSpaces/le_refl'.lean](le_refl'.lean)
- [ContinuousLattice/FunctionSpaces/le_trans'.lean](le_trans'.lean)
- [ContinuousLattice/FunctionSpaces/lt.lean](lt.lean)
- [ContinuousLattice/FunctionSpaces/lt_iff_le_not_ge'.lean](lt_iff_le_not_ge'.lean)
- [ContinuousLattice/FunctionSpaces/BasicInst28.lean](BasicInst28.lean)
- [ContinuousLattice/FunctionSpaces/le_def.lean](le_def.lean)
- [ContinuousLattice/FunctionSpaces/preservesDirectedSup_coe.lean](preservesDirectedSup_coe.lean)
- [ContinuousLattice/FunctionSpaces/pointwise_sSup_preservesDirectedSup.lean](pointwise_sSup_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/pointwise_sup_preservesDirectedSup.lean](pointwise_sup_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/sSupMaps_continuous.lean](sSupMaps_continuous.lean)
- [ContinuousLattice/FunctionSpaces/sSupMaps.lean](sSupMaps.lean)
- [ContinuousLattice/FunctionSpaces/BasicInst30.lean](BasicInst30.lean)
- [ContinuousLattice/FunctionSpaces/sSup_apply.lean](sSup_apply.lean)
- [ContinuousLattice/FunctionSpaces/isLUB_sSup.lean](isLUB_sSup.lean)
- [ContinuousLattice/FunctionSpaces/BasicInst33.lean](BasicInst33.lean)
- [ContinuousLattice/FunctionSpaces/idMap.lean](idMap.lean)
- [ContinuousLattice/FunctionSpaces/idMap_apply.lean](idMap_apply.lean)
- [ContinuousLattice/FunctionSpaces/comp_apply.lean](comp_apply.lean)
- [ContinuousLattice/FunctionSpaces/bot_apply.lean](bot_apply.lean)
- [ContinuousLattice/FunctionSpaces/const_apply.lean](const_apply.lean)
- [ContinuousLattice/FunctionSpaces/sSup_image_prod_mk_left.lean](sSup_image_prod_mk_left.lean)
- [ContinuousLattice/FunctionSpaces/curry_right_preservesDirectedSup.lean](curry_right_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/sSup_image_prod_mk_right.lean](sSup_image_prod_mk_right.lean)
- [ContinuousLattice/FunctionSpaces/curry_left_preservesDirectedSup.lean](curry_left_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionEvalSubbasis.lean](scottFunctionEvalSubbasis.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionTopology.lean](scottFunctionTopology.lean)
- [ContinuousLattice/FunctionSpaces/scottLambdaAt.lean](scottLambdaAt.lean)
- [ContinuousLattice/FunctionSpaces/lambda_outer_preservesDirectedSup.lean](lambda_outer_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/scottLambda.lean](scottLambda.lean)
- [ContinuousLattice/FunctionSpaces/scottLambda_apply.lean](scottLambda_apply.lean)
- [ContinuousLattice/FunctionSpaces/IsProjection.lean](IsProjection.lean)
- [ContinuousLattice/FunctionSpaces/Projections.lean](Projections.lean)
- [ContinuousLattice/FunctionSpaces/ambientSSup.lean](ambientSSup.lean)
- [ContinuousLattice/FunctionSpaces/converseRetr.lean](converseRetr.lean)
- [ContinuousLattice/FunctionSpaces/converseRetr_mono.lean](converseRetr_mono.lean)
- [ContinuousLattice/FunctionSpaces/converseRetr_preservesDirectedSup.lean](converseRetr_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/incl_converseRetr_le.lean](incl_converseRetr_le.lean)
- [ContinuousLattice/FunctionSpaces/incl_sup_of_preservesSSup.lean](incl_sup_of_preservesSSup.lean)
- [ContinuousLattice/FunctionSpaces/incl_mono_of_preservesSSup.lean](incl_mono_of_preservesSSup.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_iff.lean](isProjection_iff.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_bot.lean](isProjection_bot.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_directedSup.lean](isProjection_directedSup.lean)
- [ContinuousLattice/FunctionSpaces/le_of_incl_le.lean](le_of_incl_le.lean)
- [ContinuousLattice/FunctionSpaces/converseRetr_incl.lean](converseRetr_incl.lean)
- [ContinuousLattice/FunctionSpaces/converseProjection.lean](converseProjection.lean)
- [ContinuousLattice/FunctionSpaces/scottMapInducedPiTopology.lean](scottMapInducedPiTopology.lean)
- [ContinuousLattice/FunctionSpaces/scottMapPointwiseSubbasis.lean](scottMapPointwiseSubbasis.lean)
- [ContinuousLattice/FunctionSpaces/scottMapPointwiseTopology.lean](scottMapPointwiseTopology.lean)
- [ContinuousLattice/FunctionSpaces/stepFun.lean](stepFun.lean)
- [ContinuousLattice/FunctionSpaces/stepFun_of_not_wayBelow.lean](stepFun_of_not_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/stepFun_of_wayBelow.lean](stepFun_of_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/stepFun_preservesDirectedSup.lean](stepFun_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/stepMap.lean](stepMap.lean)
- [ContinuousLattice/FunctionSpaces/sup.lean](sup.lean)
- [ContinuousLattice/FunctionSpaces/finsetSupOf.lean](finsetSupOf.lean)
- [ContinuousLattice/FunctionSpaces/directedOn_finsetSupOf.lean](directedOn_finsetSupOf.lean)
- [ContinuousLattice/FunctionSpaces/mem_finsetSupOf_of_mem.lean](mem_finsetSupOf_of_mem.lean)
- [ContinuousLattice/FunctionSpaces/le_sSup_finsetSupOf.lean](le_sSup_finsetSupOf.lean)
- [ContinuousLattice/FunctionSpaces/sSup_le_finsetSupOf.lean](sSup_le_finsetSupOf.lean)
- [ContinuousLattice/FunctionSpaces/sSup_finsetSupOf.lean](sSup_finsetSupOf.lean)
- [ContinuousLattice/FunctionSpaces/sup_apply.lean](sup_apply.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_sup.lean](isProjection_sup.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_finsetSup.lean](isProjection_finsetSup.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_sSup.lean](isProjection_sSup.lean)
- [ContinuousLattice/FunctionSpaces/instSupSet.lean](instSupSet.lean)
- [ContinuousLattice/FunctionSpaces/Basic/isLUB_sSup.lean](Basic/isLUB_sSup.lean)
- [ContinuousLattice/FunctionSpaces/instCompleteLattice.lean](instCompleteLattice.lean)
- [ContinuousLattice/FunctionSpaces/con_.lean](con_.lean)
- [ContinuousLattice/FunctionSpaces/con_apply.lean](con_apply.lean)
- [ContinuousLattice/FunctionSpaces/min.lean](min.lean)
- [ContinuousLattice/FunctionSpaces/min_apply.lean](min_apply.lean)
- [ContinuousLattice/FunctionSpaces/projection.lean](projection.lean)
- [ContinuousLattice/FunctionSpaces/toOrderHom.lean](toOrderHom.lean)
- [ContinuousLattice/FunctionSpaces/fix.lean](fix.lean)
- [ContinuousLattice/FunctionSpaces/fix_eq.lean](fix_eq.lean)
- [ContinuousLattice/FunctionSpaces/fix_le.lean](fix_le.lean)
- [ContinuousLattice/FunctionSpaces/fix_mono.lean](fix_mono.lean)
- [ContinuousLattice/FunctionSpaces/fix_preservesDirectedSup.lean](fix_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/fixMap.lean](fixMap.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3_sSup.lean](theorem_3_3_sSup.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3_sup.lean](theorem_3_3_sup.lean)
