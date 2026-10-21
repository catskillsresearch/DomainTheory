# Exercise 8.25

**EXERCISE 8.25.** The problem is to find non-trivial solutions to the domain equation
$$
(\spadesuit) \qquad D \cong D \to D.
$$
Show that the "obvious" solution by retracts is of no use because
$$
1 \to 1 = 1
$$
for projections. Change the method as follows. Show first
$$
U^\infty \times U^\infty \cong U^\infty.
$$
Next solve
$$
D \cong D \to U^\infty
$$
and remark that $U \triangleleft D$; so $D$ is universal and non-trivial. Finally prove $(\spadesuit)$ for this $D$. (Hint: First show
$$
D \times D \cong D,
$$
and then show $D$ satisfies $(\spadesuit)$.) Is this $D$ effectively given?

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825.lean](Exercise825.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825/Basic.lean](Exercise825/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825/exercise_8_25.lean](Exercise825/exercise_8_25.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825/exercise_8_25_universal.lean](Exercise825/exercise_8_25_universal.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Closing.lean](Exercise825Closing.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Closing/Basic.lean](Exercise825Closing/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Closing/funSpace_self_isomorphic.lean](Exercise825Closing/funSpace_self_isomorphic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Closing/prod_self_isomorphic.lean](Exercise825Closing/prod_self_isomorphic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr.lean](Exercise825Congr.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/Basic.lean](Exercise825Congr/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/curry_isomorphic.lean](Exercise825Congr/curry_isomorphic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/funSpaceCongrOrderIso.lean](Exercise825Congr/funSpaceCongrOrderIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/funSpaceCongr_hij.lean](Exercise825Congr/funSpaceCongr_hij.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/funSpaceCongr_hji.lean](Exercise825Congr/funSpaceCongr_hji.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/funSpace_congr.lean](Exercise825Congr/funSpace_congr.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/funSpace_congr_left.lean](Exercise825Congr/funSpace_congr_left.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/funSpace_congr_right.lean](Exercise825Congr/funSpace_congr_right.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/ofIso_comp_ofIso_symm.lean](Exercise825Congr/ofIso_comp_ofIso_symm.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/ofIso_symm_comp_ofIso.lean](Exercise825Congr/ofIso_symm_comp_ofIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Congr/orderIsoOfMutualInverse.lean](Exercise825Congr/orderIsoOfMutualInverse.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Embed.lean](Exercise825Embed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Embed/Basic.lean](Exercise825Embed/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Embed/component_embedIntoPow_succ.lean](Exercise825Embed/component_embedIntoPow_succ.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Embed/component_embedIntoPow_zero.lean](Exercise825Embed/component_embedIntoPow_zero.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Embed/embedIntoPow.lean](Exercise825Embed/embedIntoPow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Embed/embedIntoPow_comp_head_le.lean](Exercise825Embed/embedIntoPow_comp_head_le.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Embed/head_comp_embedIntoPow.lean](Exercise825Embed/head_comp_embedIntoPow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Embed/toElementMap_embedIntoPow.lean](Exercise825Embed/toElementMap_embedIntoPow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Embed/trianglelefteq_iterSys.lean](Exercise825Embed/trianglelefteq_iterSys.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint.lean](Exercise825FixedPoint.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/Basic.lean](Exercise825FixedPoint/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/Dsol_isomorphic_funSpace_cCombinator.lean](Exercise825FixedPoint/Dsol_isomorphic_funSpace_cCombinator.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/RDom.lean](Exercise825FixedPoint/RDom.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/RMap.lean](Exercise825FixedPoint/RMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/TArrow.lean](Exercise825FixedPoint/TArrow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/U_trianglelefteq_Dsol.lean](Exercise825FixedPoint/U_trianglelefteq_Dsol.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/cCombinator.lean](Exercise825FixedPoint/cCombinator.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/cElementIso.lean](Exercise825FixedPoint/cElementIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/cInj.lean](Exercise825FixedPoint/cInj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/cInj_comp_cProj_le.lean](Exercise825FixedPoint/cInj_comp_cProj_le.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/cProj.lean](Exercise825FixedPoint/cProj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/cProj_comp_cInj.lean](Exercise825FixedPoint/cProj_comp_cInj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/curryOnceC.lean](Exercise825FixedPoint/curryOnceC.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/exercise_8_25_main.lean](Exercise825FixedPoint/exercise_8_25_main.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/fixedNbhd_cCombinator_isomorphic.lean](Exercise825FixedPoint/fixedNbhd_cCombinator_isomorphic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/fixedNbhd_elementIso_fix.lean](Exercise825FixedPoint/fixedNbhd_elementIso_fix.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/hT_TArrow.lean](Exercise825FixedPoint/hT_TArrow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/hVV_cCombinator.lean](Exercise825FixedPoint/hVV_cCombinator.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/ht_tOpMap.lean](Exercise825FixedPoint/ht_tOpMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/isFinitaryProjection_cCombinator.lean](Exercise825FixedPoint/isFinitaryProjection_cCombinator.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/isFinitary_cCombinator.lean](Exercise825FixedPoint/isFinitary_cCombinator.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/isProjection_cCombinator.lean](Exercise825FixedPoint/isProjection_cCombinator.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/isRetraction_cCombinator.lean](Exercise825FixedPoint/isRetraction_cCombinator.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/lamOp.lean](Exercise825FixedPoint/lamOp.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/presentationIterU.lean](Exercise825FixedPoint/presentationIterU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/tOpMap.lean](Exercise825FixedPoint/tOpMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/tOp_tOpMap.lean](Exercise825FixedPoint/tOp_tOpMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/toApproxMap_lamOp.lean](Exercise825FixedPoint/toApproxMap_lamOp.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825FixedPoint/toElementMap_RMap.lean](Exercise825FixedPoint/toElementMap_RMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Pow.lean](Exercise825Pow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Pow/Basic.lean](Exercise825Pow/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Pow/arrowReindexOrderIso.lean](Exercise825Pow/arrowReindexOrderIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Pow/interleaveOrderIso.lean](Exercise825Pow/interleaveOrderIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Pow/powProdOrderIso.lean](Exercise825Pow/powProdOrderIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Pow/pow_prod_isomorphic.lean](Exercise825Pow/pow_prod_isomorphic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Pow/sumArrowOrderIso.lean](Exercise825Pow/sumArrowOrderIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Unit.lean](Exercise825Unit.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Unit/Basic.lean](Exercise825Unit/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Unit/funSpace_unitSys_isomorphic.lean](Exercise825Unit/funSpace_unitSys_isomorphic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Unit/isoOfUnique.lean](Exercise825Unit/isoOfUnique.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise825Unit/isomorphic_of_unique.lean](Exercise825Unit/isomorphic_of_unique.lean)
