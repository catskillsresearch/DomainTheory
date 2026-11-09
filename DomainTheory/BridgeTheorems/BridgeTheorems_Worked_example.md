# Worked example — S-expressions / trees

**Dependencies.** Inside WorkedExampleSExpr, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. BridgeTheorems is the Lean files in that chapter folder, not in a subfolder. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "WorkedExampleSExpr/WorkedExampleSExpr.mermaid"

@import "BridgeTheorems_Worked_example.english" {code_block=false}

**[InformationSystems/InformationSystems/lowerBoundEnt.lean](../InformationSystems/InformationSystems/lowerBoundEnt.lean)**

@import "../InformationSystems/InformationSystems/lowerBoundEnt.lean"
**[InformationSystems/InformationSystems/a_first_example.lean](../InformationSystems/InformationSystems/a_first_example.lean)**

@import "../InformationSystems/InformationSystems/a_first_example.lean"
**[BridgeTheorems/unfoldInsert.lean](unfoldInsert.lean)**

@import "unfoldInsert.lean"
**[BridgeTheorems/SexDomainEquationInst10.lean](SexDomainEquationInst10.lean)**

@import "SexDomainEquationInst10.lean"
**[BridgeTheorems/mem_foldr_unfold.lean](mem_foldr_unfold.lean)**

@import "mem_foldr_unfold.lean"
**[BridgeTheorems/TreeProd.lean](TreeProd.lean)**

@import "TreeProd.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/idMap.lean](../InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/idMap.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/idMap.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition54.lean](../InformationSystems/ApproximableMappingsBetweenDomains/Proposition54.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition54.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Approximable/comp.lean](../InformationSystems/ApproximableMappingsBetweenDomains/Approximable/comp.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Approximable/comp.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/proposition_5_5.lean](../InformationSystems/ApproximableMappingsBetweenDomains/proposition_5_5.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/proposition_5_5.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/instLeftCommutativeLiftSumLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/instLeftCommutativeLiftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/instLeftCommutativeLiftSumLeft.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/fix_under_intertwining.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/fix_under_intertwining.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/fix_under_intertwining.lean"
**[InformationSystems/FunctionSpaceAsADomain/proposition_7_4.lean](../InformationSystems/FunctionSpaceAsADomain/proposition_7_4.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/proposition_7_4.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/PEnt.lean](../InformationSystems/SomeDomainEquations/Factoid84/PEnt.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/PEnt.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/P.lean](../InformationSystems/SomeDomainEquations/Factoid84/P.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/P.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/topElement.lean](../InformationSystems/SomeDomainEquations/Factoid84/topElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/topElement.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/mkLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/mkLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/mkLeft.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/botElement.lean](../InformationSystems/SomeDomainEquations/Factoid84/botElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/botElement.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/constMap.lean](../InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/constMap.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/constMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/not_mem_right_of_mem_left.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/not_mem_right_of_mem_left.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/not_mem_right_of_mem_left.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/mkLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/mkLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/mkLeft.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition56.lean](../InformationSystems/ApproximableMappingsBetweenDomains/Proposition56.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition56.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitSystem.lean](../InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitSystem.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitSystem.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65/toElement_constMap_bot.lean](../InformationSystems/ProductsAndSumsOfDomains/Factoid65/toElement_constMap_bot.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65/toElement_constMap_bot.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65.lean](../InformationSystems/ProductsAndSumsOfDomains/Factoid65.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/bar.lean](../InformationSystems/SomeDomainEquations/Factoid84/bar.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/bar.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/barElement.lean](../InformationSystems/SomeDomainEquations/Factoid84/barElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/barElement.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/BotApprox.lean](../InformationSystems/SomeDomainEquations/Factoid84/BotApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/BotApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/ConsistentApprox.lean](../InformationSystems/SomeDomainEquations/Factoid84/ConsistentApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/ConsistentApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/RogueApprox.lean](../InformationSystems/SomeDomainEquations/Factoid84/RogueApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/RogueApprox.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/instLeftCommutativeLiftSumRight.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/instLeftCommutativeLiftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/instLeftCommutativeLiftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/liftSumLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/lft_mem_Con_of_SumCon_rht_empty.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/lft_mem_Con_of_SumCon_rht_empty.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/lft_mem_Con_of_SumCon_rht_empty.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/sumLftCarrier.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/sumLftCarrier.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/sumLftCarrier.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/rht_mem_Con_of_SumCon_lft_empty.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/rht_mem_Con_of_SumCon_lft_empty.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/rht_mem_Con_of_SumCon_lft_empty.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/mem_foldr_liftSumRight.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/mem_foldr_liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/mem_foldr_liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_rht_of_sumEntSet.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_rht_of_sumEntSet.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_rht_of_sumEntSet.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/mem_foldr_liftSumLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/mem_foldr_liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/mem_foldr_liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/rht_eq_empty_of_sumEntSet.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/rht_eq_empty_of_sumEntSet.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/rht_eq_empty_of_sumEntSet.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/lft_eq_empty_of_sumEntSet.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/lft_eq_empty_of_sumEntSet.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/lft_eq_empty_of_sumEntSet.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/copair_union_disj.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/copair_union_disj.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/copair_union_disj.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/liftSumRight.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/mem_liftSumRight.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/mem_liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/mem_liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_liftSumRight.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/mem_liftSumLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/mem_liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/mem_liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_liftSumLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/sumRhtCarrier.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/sumRhtCarrier.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/sumRhtCarrier.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitElement_eq_bot.lean](../InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitElement_eq_bot.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitElement_eq_bot.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_from_unit_eq_const.lean](../InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_from_unit_eq_const.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_from_unit_eq_const.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_liftSumLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/sumElementLft.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/sumElementLft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/sumElementLft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_liftSumRight.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/sumElementRht.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/sumElementRht.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/sumElementRht.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/inrMap.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/inrMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/inrMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/mkRight.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/mkRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/mkRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/ProdCon.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/ProdCon.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/ProdCon.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/productSystem.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/productSystem.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/productSystem.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/liftRight.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/liftRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/liftRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/pairMap.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/pairMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/pairMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/productSystem_more.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/productSystem_more.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/productSystem_more.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/liftRight.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/liftRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/liftRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_to_unit_eq_const.lean](../InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_to_unit_eq_const.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_to_unit_eq_const.lean"
**[BridgeTheorems/unfoldFinset.lean](unfoldFinset.lean)**

@import "unfoldFinset.lean"
**[BridgeTheorems/mem_unfoldFinset.lean](mem_unfoldFinset.lean)**

@import "mem_unfoldFinset.lean"
**[BridgeTheorems/treeFold.lean](treeFold.lean)**

@import "treeFold.lean"
**[BridgeTheorems/treeFold_eq_or_pairBots.lean](treeFold_eq_or_pairBots.lean)**

@import "treeFold_eq_or_pairBots.lean"
**[BridgeTheorems/foldInsert.lean](foldInsert.lean)**

@import "foldInsert.lean"
**[BridgeTheorems/SexDomainEquationInst15.lean](SexDomainEquationInst15.lean)**

@import "SexDomainEquationInst15.lean"
**[BridgeTheorems/lftFinset_image_unfold.lean](lftFinset_image_unfold.lean)**

@import "lftFinset_image_unfold.lean"
**[BridgeTheorems/rhtFinset_image_unfold_mem.lean](rhtFinset_image_unfold_mem.lean)**

@import "rhtFinset_image_unfold_mem.lean"
**[BridgeTheorems/foldFinset.lean](foldFinset.lean)**

@import "foldFinset.lean"
**[BridgeTheorems/SumCon_image_treeCon.lean](SumCon_image_treeCon.lean)**

@import "SumCon_image_treeCon.lean"
**[BridgeTheorems/TreeCon_image_sumCon.lean](TreeCon_image_sumCon.lean)**

@import "TreeCon_image_sumCon.lean"
**[BridgeTheorems/TreeEnt_sumEnt.lean](TreeEnt_sumEnt.lean)**

@import "TreeEnt_sumEnt.lean"
**[BridgeTheorems/foldElement.lean](foldElement.lean)**

@import "foldElement.lean"
**[BridgeTheorems/TreeEnt_pairL_bot_of_pairs.lean](TreeEnt_pairL_bot_of_pairs.lean)**

@import "TreeEnt_pairL_bot_of_pairs.lean"
**[BridgeTheorems/mem_foldr_fold.lean](mem_foldr_fold.lean)**

@import "mem_foldr_fold.lean"
**[BridgeTheorems/TreeEnt_pairR_bot_of_pairs.lean](TreeEnt_pairR_bot_of_pairs.lean)**

@import "TreeEnt_pairR_bot_of_pairs.lean"
**[BridgeTheorems/mem_closed_pair_bots.lean](mem_closed_pair_bots.lean)**

@import "mem_closed_pair_bots.lean"
**[BridgeTheorems/saturated_of_closed.lean](saturated_of_closed.lean)**

@import "saturated_of_closed.lean"
**[BridgeTheorems/mem_foldFinset.lean](mem_foldFinset.lean)**

@import "mem_foldFinset.lean"
**[InformationSystems/FunctionSpaceAsADomain/proposition_7_4.lean](../InformationSystems/FunctionSpaceAsADomain/proposition_7_4.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/proposition_7_4.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/liftLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/pairMap.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/pairMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/pairMap.lean"
**[BridgeTheorems/SumEnt_treeFold.lean](SumEnt_treeFold.lean)**

@import "SumEnt_treeFold.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Product/pairMap.lean](../InformationSystems/ProductsAndSumsOfDomains/Product/pairMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Product/pairMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/proposition_6_2.lean](../InformationSystems/ProductsAndSumsOfDomains/proposition_6_2.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/proposition_6_2.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/liftPair.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/ProdCon_liftPair.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/ProdCon_liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/ProdCon_liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/fstFinset_liftPair.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/fstFinset_liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/fstFinset_liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mkFunToken.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mkFunToken.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mkFunToken.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/applyMap.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/applyMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/applyMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/sndFinset_liftPair.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/sndFinset_liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/sndFinset_liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/entSet_liftPair.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/entSet_liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/entSet_liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairElements.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/uncurryMap.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/uncurryMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/uncurryMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/rel_input_output_union.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/rel_input_output_union.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/rel_input_output_union.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/funCon_of_approxMap.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/funCon_of_approxMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/funCon_of_approxMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/approxMap_toElement.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/approxMap_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/approxMap_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/element_toApproxMap.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/element_toApproxMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/element_toApproxMap.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/ReflApprox.lean](../InformationSystems/SomeDomainEquations/Factoid84/ReflApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/ReflApprox.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_lft_of_sumEntSet.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_lft_of_sumEntSet.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_lft_of_sumEntSet.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/inlMap.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/inlMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/inlMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/copairMap.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/copairMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/copairMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_liftSumRight.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_liftRht_of_right_only.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_liftRht_of_right_only.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_liftRht_of_right_only.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_liftSumLeft.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_u_of_inr_witness.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_u_of_inr_witness.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_u_of_inr_witness.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_eq_empty_or_mem.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_eq_empty_or_mem.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_eq_empty_or_mem.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_eq_empty_or_mem.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_eq_empty_or_mem.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_eq_empty_or_mem.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/eq_botElement_of_no_injections.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/eq_botElement_of_no_injections.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/eq_botElement_of_no_injections.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_liftLft_of_left_only.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_liftLft_of_left_only.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_liftLft_of_left_only.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/comp_copairMap_inrMap.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/comp_copairMap_inrMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/comp_copairMap_inrMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/subset_botElement_of_projections_empty.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/subset_botElement_of_projections_empty.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/subset_botElement_of_projections_empty.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_empty_of_rel_bot_like.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_empty_of_rel_bot_like.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_empty_of_rel_bot_like.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_u_of_inl_witness.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_u_of_inl_witness.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/entSet_u_of_inl_witness.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/copairMap_unique.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/copairMap_unique.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/copairMap_unique.lean"
**[InformationSystems/ProductsAndSumsOfDomains/proposition_6_4.lean](../InformationSystems/ProductsAndSumsOfDomains/proposition_6_4.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/proposition_6_4.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Sum/comp_copairMap_inlMap.lean](../InformationSystems/ProductsAndSumsOfDomains/Sum/comp_copairMap_inlMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Sum/comp_copairMap_inlMap.lean"
**[BridgeTheorems/treeUnfold_treeFold.lean](treeUnfold_treeFold.lean)**

@import "treeUnfold_treeFold.lean"
**[BridgeTheorems/unfoldFinset_foldFinset.lean](unfoldFinset_foldFinset.lean)**

@import "unfoldFinset_foldFinset.lean"
**[BridgeTheorems/unfoldElement.lean](unfoldElement.lean)**

@import "unfoldElement.lean"
**[BridgeTheorems/unfoldElement_foldElement.lean](unfoldElement_foldElement.lean)**

@import "unfoldElement_foldElement.lean"
**[BridgeTheorems/foldElement_unfoldElement.lean](foldElement_unfoldElement.lean)**

@import "foldElement_unfoldElement.lean"
**[BridgeTheorems/treeDomainIso.lean](treeDomainIso.lean)**

@import "treeDomainIso.lean"
**[BridgeTheorems/SexDomainEquation.lean](SexDomainEquation.lean)**

@import "SexDomainEquation.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/rel_of_funTokens.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/rel_of_funTokens.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/rel_of_funTokens.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/funCon_of_curry_pointwise.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/funCon_of_curry_pointwise.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/funCon_of_curry_pointwise.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/curryMap.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/curryMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/curryMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/approxMap_toElement_element_toApproxMap.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/approxMap_toElement_element_toApproxMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/approxMap_toElement_element_toApproxMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/theorem_7_2.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/theorem_7_2.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/theorem_7_2.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/sndMap_pairElements.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/sndMap_pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/sndMap_pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_pairElements_liftRight.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_pairElements_liftRight.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_pairElements_liftRight.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/liftLeft_funion.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/liftLeft_funion.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/liftLeft_funion.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_snd_of_subset_pairElements.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_snd_of_subset_pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_snd_of_subset_pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_approxMap_toElement.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_approxMap_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_approxMap_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/liftRight_funion.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/liftRight_funion.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/liftRight_funion.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/uncurry_curryMap.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/uncurry_curryMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/uncurry_curryMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/fstMap_pairElements.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/fstMap_pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/fstMap_pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_pairElements_liftLeft.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_pairElements_liftLeft.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_pairElements_liftLeft.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_fst_of_subset_pairElements.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_fst_of_subset_pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_fst_of_subset_pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_pairElements_liftPair.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_pairElements_liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_pairElements_liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/applyMap_toElement.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/applyMap_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/applyMap_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/curryMap_unique.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/curryMap_unique.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/curryMap_unique.lean"
**[InformationSystems/FunctionSpaceAsADomain/theorem_7_2.lean](../InformationSystems/FunctionSpaceAsADomain/theorem_7_2.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/theorem_7_2.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/InfoSysObj.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/InfoSysObj.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/InfoSysObj.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/unit.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/unit.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/unit.lean"
**[BridgeTheorems/InfoSysConstructions/sum_element_trichotomy.lean](InfoSysConstructions/sum_element_trichotomy.lean)**

@import "InfoSysConstructions/sum_element_trichotomy.lean"
**[BridgeTheorems/InfoSysConstructions/not_left_mem_sum_botElement.lean](InfoSysConstructions/not_left_mem_sum_botElement.lean)**

@import "InfoSysConstructions/not_left_mem_sum_botElement.lean"
**[BridgeTheorems/InfoSysConstructions/lftFinset_singleton_right.lean](InfoSysConstructions/lftFinset_singleton_right.lean)**

@import "InfoSysConstructions/lftFinset_singleton_right.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairOpUncurry.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairOpUncurry.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairOpUncurry.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixChain.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixChain.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixChain.lean"
**[BridgeTheorems/InfoSysConstructions/rhtFinset_singleton_left.lean](InfoSysConstructions/rhtFinset_singleton_left.lean)**

@import "InfoSysConstructions/rhtFinset_singleton_left.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_empty.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_empty.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_empty.lean"
**[BridgeTheorems/InfoSysConstructions/not_right_mem_sum_botElement.lean](InfoSysConstructions/not_right_mem_sum_botElement.lean)**

@import "InfoSysConstructions/not_right_mem_sum_botElement.lean"
**[BridgeTheorems/InfoSysConstructions/pairElements_unpair.lean](InfoSysConstructions/pairElements_unpair.lean)**

@import "InfoSysConstructions/pairElements_unpair.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/id_acomp.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/id_acomp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/id_acomp.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/instCategoryInfoSysObj.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/instCategoryInfoSysObj.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/instCategoryInfoSysObj.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/terminalLimitCone.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/terminalLimitCone.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/terminalLimitCone.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/compOpUncurry.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/compOpUncurry.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/compOpUncurry.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/BoolToken.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/BoolToken.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/BoolToken.lean"
**[BridgeTheorems/InfoSysConstructions/pairElements_mono.lean](InfoSysConstructions/pairElements_mono.lean)**

@import "InfoSysConstructions/pairElements_mono.lean"
**[BridgeTheorems/InfoSysConstructions/instPartialOrderApproximableMap.lean](InfoSysConstructions/instPartialOrderApproximableMap.lean)**

@import "InfoSysConstructions/instPartialOrderApproximableMap.lean"
**[BridgeTheorems/approximableMap_scottContinuous_equiv.lean](approximableMap_scottContinuous_equiv.lean)**

@import "approximableMap_scottContinuous_equiv.lean"
**[BridgeTheorems/InfoSysConstructions/approxMap_toElement_le_iff.lean](InfoSysConstructions/approxMap_toElement_le_iff.lean)**

@import "InfoSysConstructions/approxMap_toElement_le_iff.lean"
**[BridgeTheorems/InfoSysConstructions/functionSpaceDomainIso.lean](InfoSysConstructions/functionSpaceDomainIso.lean)**

@import "InfoSysConstructions/functionSpaceDomainIso.lean"
**[BridgeTheorems/InfoSysConstructions/right_bot_mem_inrMap_toElement.lean](InfoSysConstructions/right_bot_mem_inrMap_toElement.lean)**

@import "InfoSysConstructions/right_bot_mem_inrMap_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_fst_toElement.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_fst_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_fst_toElement.lean"
**[BridgeTheorems/InfoSysConstructions/sumElementRht_inrMap_toElement.lean](InfoSysConstructions/sumElementRht_inrMap_toElement.lean)**

@import "InfoSysConstructions/sumElementRht_inrMap_toElement.lean"
**[BridgeTheorems/InfoSysConstructions/inrMap_toElement_injective.lean](InfoSysConstructions/inrMap_toElement_injective.lean)**

@import "InfoSysConstructions/inrMap_toElement_injective.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap_acomp_swapMap.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap_acomp_swapMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap_acomp_swapMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_snd_toElement.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_snd_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_snd_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/BoolPoint.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/BoolPoint.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/BoolPoint.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolSat.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolSat.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolSat.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolSystem.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolSystem.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolSystem.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_botElement_emptyEntails.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_botElement_emptyEntails.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/mem_botElement_emptyEntails.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_mono_w.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_mono_w.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_mono_w.lean"
**[BridgeTheorems/InfoSysConstructions/assembleSum.lean](InfoSysConstructions/assembleSum.lean)**

@import "InfoSysConstructions/assembleSum.lean"
**[BridgeTheorems/InfoSysConstructions/exists_assembleSum_eq.lean](InfoSysConstructions/exists_assembleSum_eq.lean)**

@import "InfoSysConstructions/exists_assembleSum_eq.lean"
**[BridgeTheorems/InfoSysConstructions/classifySum.lean](InfoSysConstructions/classifySum.lean)**

@import "InfoSysConstructions/classifySum.lean"
**[BridgeTheorems/InfoSysConstructions/assembleSum_classifySum.lean](InfoSysConstructions/assembleSum_classifySum.lean)**

@import "InfoSysConstructions/assembleSum_classifySum.lean"
**[BridgeTheorems/InfoSysConstructions/assembleSum_mono.lean](InfoSysConstructions/assembleSum_mono.lean)**

@import "InfoSysConstructions/assembleSum_mono.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/exp.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/exp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/exp.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/EmptyEntails.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/EmptyEntails.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/EmptyEntails.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/emptyEntails_empty.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/emptyEntails_empty.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/emptyEntails_empty.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictToken.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictToken.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictToken.lean"
**[BridgeTheorems/InfoSysConstructions/inrMap_toElement_le_iff.lean](InfoSysConstructions/inrMap_toElement_le_iff.lean)**

@import "InfoSysConstructions/inrMap_toElement_le_iff.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictFunToken.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictFunToken.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictFunToken.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/BasicInst22.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/BasicInst22.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/BasicInst22.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolTrue.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolTrue.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolTrue.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/toFunFinset.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/toFunFinset.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/toFunFinset.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/filter_ne_subset_of_subset_insert_strict.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/filter_ne_subset_of_subset_insert_strict.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/filter_ne_subset_of_subset_insert_strict.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/insert_filter_ne_strict.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/insert_filter_ne_strict.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/insert_filter_ne_strict.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolFalse.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolFalse.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolFalse.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictFunCon.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictFunCon.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictFunCon.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/not_ent_empty_tru.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/not_ent_empty_tru.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/not_ent_empty_tru.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictFunEnt.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictFunEnt.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/StrictFunEnt.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolCon_trichotomy.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolCon_trichotomy.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/boolCon_trichotomy.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictBot.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictBot.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictBot.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/not_ent_empty_fls.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/not_ent_empty_fls.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/not_ent_empty_fls.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/emptyEntails_funion.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/emptyEntails_funion.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/emptyEntails_funion.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictFunctionSystem.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictFunctionSystem.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictFunctionSystem.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixReach.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixReach.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixReach.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_mono_w.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_mono_w.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_mono_w.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_empty.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_empty.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_empty.lean"
**[BridgeTheorems/InfoSysConstructions/left_bot_mem_inlMap_toElement.lean](InfoSysConstructions/left_bot_mem_inlMap_toElement.lean)**

@import "InfoSysConstructions/left_bot_mem_inlMap_toElement.lean"
**[BridgeTheorems/InfoSysConstructions/sumElementLft_inlMap_toElement.lean](InfoSysConstructions/sumElementLft_inlMap_toElement.lean)**

@import "InfoSysConstructions/sumElementLft_inlMap_toElement.lean"
**[BridgeTheorems/InfoSysConstructions/inlMap_toElement_injective.lean](InfoSysConstructions/inlMap_toElement_injective.lean)**

@import "InfoSysConstructions/inlMap_toElement_injective.lean"
**[BridgeTheorems/InfoSysConstructions/assembleSum_injective.lean](InfoSysConstructions/assembleSum_injective.lean)**

@import "InfoSysConstructions/assembleSum_injective.lean"
**[BridgeTheorems/InfoSysConstructions/inlMap_toElement_le_iff.lean](InfoSysConstructions/inlMap_toElement_le_iff.lean)**

@import "InfoSysConstructions/inlMap_toElement_le_iff.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_pad.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_pad.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_pad.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/prod.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/prod.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/prod.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/productLimitCone.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/productLimitCone.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/productLimitCone.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/instCartesianMonoidalCategoryInfoSysObj.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/instCartesianMonoidalCategoryInfoSysObj.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/instCartesianMonoidalCategoryInfoSysObj.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/curryProduct.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/curryProduct.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/curryProduct.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryProduct.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryProduct.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryProduct.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorMap_eq_productMap.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorMap_eq_productMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorMap_eq_productMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHom_eq_productMap.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHom_eq_productMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHom_eq_productMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHomToProdHom.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHomToProdHom.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHomToProdHom.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_snd_toElement.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_snd_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_snd_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/pair_after_swap_toElement.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/pair_after_swap_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/pair_after_swap_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/funEnt_union_step.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/funEnt_union_step.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/funEnt_union_step.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElement_eq_productElement.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElement_eq_productElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElement_eq_productElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/prodElementToTensorElement.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/prodElementToTensorElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/prodElementToTensorElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElementToProdElement.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElementToProdElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElementToProdElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/prodHomToTensorHom.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/prodHomToTensorHom.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/prodHomToTensorHom.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/productMapToTensorMap.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/productMapToTensorMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/productMapToTensorMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorLeft_map_eq.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorLeft_map_eq.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorLeft_map_eq.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/emptyEntails_mem_botElement.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/emptyEntails_mem_botElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/emptyEntails_mem_botElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictify.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictify.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictify.lean"
**[BridgeTheorems/InfoSysConstructions/unpair.lean](InfoSysConstructions/unpair.lean)**

@import "InfoSysConstructions/unpair.lean"
**[BridgeTheorems/InfoSysConstructions/unpair_pairElements.lean](InfoSysConstructions/unpair_pairElements.lean)**

@import "InfoSysConstructions/unpair_pairElements.lean"
**[BridgeTheorems/InfoSysConstructions/productDomainIso.lean](InfoSysConstructions/productDomainIso.lean)**

@import "InfoSysConstructions/productDomainIso.lean"
**[BridgeTheorems/InfoSysConstructions/classifySum_assembleSum.lean](InfoSysConstructions/classifySum_assembleSum.lean)**

@import "InfoSysConstructions/classifySum_assembleSum.lean"
**[BridgeTheorems/InfoSysConstructions/sumDomainIso.lean](InfoSysConstructions/sumDomainIso.lean)**

@import "InfoSysConstructions/sumDomainIso.lean"
**[BridgeTheorems/InfoSysConstructions/Basic.lean](InfoSysConstructions/Basic.lean)**

@import "InfoSysConstructions/Basic.lean"
**[BridgeTheorems/InfoSysConstructions/sumElementRht_eq.lean](InfoSysConstructions/sumElementRht_eq.lean)**

@import "InfoSysConstructions/sumElementRht_eq.lean"
**[BridgeTheorems/InfoSysConstructions/sumElementLft_eq.lean](InfoSysConstructions/sumElementLft_eq.lean)**

@import "InfoSysConstructions/sumElementLft_eq.lean"
**[BridgeTheorems/InfoSysConstructions/unpair_mono.lean](InfoSysConstructions/unpair_mono.lean)**

@import "InfoSysConstructions/unpair_mono.lean"
**[BridgeTheorems/InfoSysConstructions.lean](InfoSysConstructions.lean)**

@import "InfoSysConstructions.lean"
**[BridgeTheorems/ScottMapBridge.lean](ScottMapBridge.lean)**

@import "ScottMapBridge.lean"
**[BridgeTheorems/WorkedExampleSExpr/lowerBoundSystem.lean](WorkedExampleSExpr/lowerBoundSystem.lean)**

@import "WorkedExampleSExpr/lowerBoundSystem.lean"
**[BridgeTheorems/WorkedExampleSExpr/SexSys.lean](WorkedExampleSExpr/SexSys.lean)**

@import "WorkedExampleSExpr/SexSys.lean"
**[BridgeTheorems/WorkedExampleSExpr/SexRhs.lean](WorkedExampleSExpr/SexRhs.lean)**

@import "WorkedExampleSExpr/SexRhs.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexRhsSemanticIso.lean](WorkedExampleSExpr/sexRhsSemanticIso.lean)**

@import "WorkedExampleSExpr/sexRhsSemanticIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso.lean](WorkedExampleSExpr/sexDomainEquationIso.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexAtom.lean](WorkedExampleSExpr/sexAtom.lean)**

@import "WorkedExampleSExpr/sexAtom.lean"
**[BridgeTheorems/WorkedExampleSExpr/Basic.lean](WorkedExampleSExpr/Basic.lean)**

@import "WorkedExampleSExpr/Basic.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexAtom_mem_self.lean](WorkedExampleSExpr/sexAtom_mem_self.lean)**

@import "WorkedExampleSExpr/sexAtom_mem_self.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexIdealIso.lean](WorkedExampleSExpr/exists_sexIdealIso.lean)**

@import "WorkedExampleSExpr/exists_sexIdealIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_fold.lean](WorkedExampleSExpr/sexDomainEquationIso_fold.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso_fold.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_unfold.lean](WorkedExampleSExpr/sexDomainEquationIso_unfold.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso_unfold.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexId_toElement.lean](WorkedExampleSExpr/sexId_toElement.lean)**

@import "WorkedExampleSExpr/sexId_toElement.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexDomainEquationIso.lean](WorkedExampleSExpr/exists_sexDomainEquationIso.lean)**

@import "WorkedExampleSExpr/exists_sexDomainEquationIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexUnfold_atom.lean](WorkedExampleSExpr/sexUnfold_atom.lean)**

@import "WorkedExampleSExpr/sexUnfold_atom.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexRhs_eq_sum_product.lean](WorkedExampleSExpr/sexRhs_eq_sum_product.lean)**

@import "WorkedExampleSExpr/sexRhs_eq_sum_product.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/curry_uncurry.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/curry_uncurry.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/curry_uncurry.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexNeighborhoodIso.lean](WorkedExampleSExpr/exists_sexNeighborhoodIso.lean)**

@import "WorkedExampleSExpr/exists_sexNeighborhoodIso.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/constOp.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/constOp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/constOp.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairOp.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairOp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairOp.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/compOp.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/compOp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/compOp.lean"
**[InformationSystems/FunctionSpaceAsADomain/theorem_76.lean](../InformationSystems/FunctionSpaceAsADomain/theorem_76.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/theorem_76.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairMap_toElement_pairElements.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairMap_toElement_pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/pairMap_toElement_pairElements.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/IdemApprox.lean](../InformationSystems/SomeDomainEquations/Factoid84/IdemApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/IdemApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/IsDomainApprox.lean](../InformationSystems/SomeDomainEquations/Factoid84/IsDomainApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/IsDomainApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/scottCon.lean](../InformationSystems/SomeDomainEquations/Factoid84/scottCon.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/scottCon.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/mem_topElement.lean](../InformationSystems/SomeDomainEquations/Factoid84/mem_topElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/mem_topElement.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/flatRel.lean](../InformationSystems/SomeDomainEquations/Factoid84/flatRel.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/flatRel.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/mem_barElement.lean](../InformationSystems/SomeDomainEquations/Factoid84/mem_barElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/mem_barElement.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/BotApprox_any.lean](../InformationSystems/SomeDomainEquations/Factoid84/BotApprox_any.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/BotApprox_any.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/flatMap.lean](../InformationSystems/SomeDomainEquations/Factoid84/flatMap.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/flatMap.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/DomainApprox.lean](../InformationSystems/SomeDomainEquations/Factoid84/DomainApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/DomainApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/flatDomainApprox.lean](../InformationSystems/SomeDomainEquations/Factoid84/flatDomainApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/flatDomainApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/not_RogueApprox_idMap.lean](../InformationSystems/SomeDomainEquations/Factoid84/not_RogueApprox_idMap.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/not_RogueApprox_idMap.lean"
**[InformationSystems/SomeDomainEquations/Factoid84.lean](../InformationSystems/SomeDomainEquations/Factoid84.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/mem_botElement.lean](../InformationSystems/SomeDomainEquations/Factoid84/mem_botElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/mem_botElement.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/barElement_zero_eq_bot.lean](../InformationSystems/SomeDomainEquations/Factoid84/barElement_zero_eq_bot.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/barElement_zero_eq_bot.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/scottCon_empty_iff_consistent.lean](../InformationSystems/SomeDomainEquations/Factoid84/scottCon_empty_iff_consistent.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/scottCon_empty_iff_consistent.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_con.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_con.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_con.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_union.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_union.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_union.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_union.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_union.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_union.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_con.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_con.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_con.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/Basic.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/Basic.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/Basic.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_subset_pre_fixed.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_subset_pre_fixed.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_subset_pre_fixed.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_step_of_rel.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_step_of_rel.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_step_of_rel.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/toElement_fixElement_le.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/toElement_fixElement_le.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/toElement_fixElement_le.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_le_of_pre_fixed.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_le_of_pre_fixed.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_le_of_pre_fixed.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_fixed.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_fixed.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_fixed.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_unique.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_unique.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_unique.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap_unique.lean](../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap_unique.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap_unique.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_of_entSet_mem.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_of_entSet_mem.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/subset_of_entSet_mem.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/condMap.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/condMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/condMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/IsStrict.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/IsStrict.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/IsStrict.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/IsStrictToken_of_IsStrict.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/IsStrictToken_of_IsStrict.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/IsStrictToken_of_IsStrict.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/approxMap_toStrictElement.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/approxMap_toStrictElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/approxMap_toStrictElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictifyElement.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictifyElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/strictifyElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/condElement.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/condElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/condElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/condMap_unique.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/condMap_unique.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/condMap_unique.lean"
**[InformationSystems/FunctionSpaceAsADomain/FunctionSpace/conditional_iso.lean](../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/conditional_iso.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/FunctionSpace/conditional_iso.lean"
**[InformationSystems/FunctionSpaceAsADomain/theorem_75.lean](../InformationSystems/FunctionSpaceAsADomain/theorem_75.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/theorem_75.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_fst_toElement.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_fst_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_fst_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryRight.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryRight.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryRight.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight_uncurryRight.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight_uncurryRight.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight_uncurryRight.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpEquiv.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpEquiv.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpEquiv.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpAdjunction.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpAdjunction.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpAdjunction.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/Basic.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/Basic.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/Basic.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor_obj.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor_obj.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor_obj.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorObj_eq_prod.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorObj_eq_prod.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorObj_eq_prod.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/ihom_obj_eq_exp.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77/ihom_obj_eq_exp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/ihom_obj_eq_exp.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77.lean](../InformationSystems/FunctionSpaceAsADomain/Factoid77.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77.lean"
