# Worked example — S-expressions / trees

**Dependencies.** Inside WorkedExampleSExpr, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. BridgeTheorems is the Lean files in that chapter folder, not in a subfolder. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "WorkedExampleSExpr/WorkedExampleSExpr.mermaid"

@import "BridgeTheorems_Worked_example.english" {code_block=false}

**[BridgeTheorems/treeFold.lean](DomainTheory/BridgeTheorems/treeFold.lean)**

@import "treeFold.lean"
**[BridgeTheorems/treeUnfold_treeFold.lean](DomainTheory/BridgeTheorems/treeUnfold_treeFold.lean)**

@import "treeUnfold_treeFold.lean"
**[BridgeTheorems/treeFold_eq_or_pairBots.lean](DomainTheory/BridgeTheorems/treeFold_eq_or_pairBots.lean)**

@import "treeFold_eq_or_pairBots.lean"
**[BridgeTheorems/unfoldInsert.lean](DomainTheory/BridgeTheorems/unfoldInsert.lean)**

@import "unfoldInsert.lean"
**[BridgeTheorems/SexDomainEquationInst10.lean](DomainTheory/BridgeTheorems/SexDomainEquationInst10.lean)**

@import "SexDomainEquationInst10.lean"
**[BridgeTheorems/foldInsert.lean](DomainTheory/BridgeTheorems/foldInsert.lean)**

@import "foldInsert.lean"
**[BridgeTheorems/SexDomainEquationInst15.lean](DomainTheory/BridgeTheorems/SexDomainEquationInst15.lean)**

@import "SexDomainEquationInst15.lean"
**[BridgeTheorems/unfoldFinset.lean](DomainTheory/BridgeTheorems/unfoldFinset.lean)**

@import "unfoldFinset.lean"
**[BridgeTheorems/foldFinset.lean](DomainTheory/BridgeTheorems/foldFinset.lean)**

@import "foldFinset.lean"
**[BridgeTheorems/mem_foldr_unfold.lean](DomainTheory/BridgeTheorems/mem_foldr_unfold.lean)**

@import "mem_foldr_unfold.lean"
**[BridgeTheorems/TreeProd.lean](DomainTheory/BridgeTheorems/TreeProd.lean)**

@import "TreeProd.lean"
**[BridgeTheorems/mem_foldr_fold.lean](DomainTheory/BridgeTheorems/mem_foldr_fold.lean)**

@import "mem_foldr_fold.lean"
**[BridgeTheorems/TreeEnt_pairR_bot_of_pairs.lean](DomainTheory/BridgeTheorems/TreeEnt_pairR_bot_of_pairs.lean)**

@import "TreeEnt_pairR_bot_of_pairs.lean"
**[BridgeTheorems/mem_unfoldFinset.lean](DomainTheory/BridgeTheorems/mem_unfoldFinset.lean)**

@import "mem_unfoldFinset.lean"
**[BridgeTheorems/lftFinset_image_unfold.lean](DomainTheory/BridgeTheorems/lftFinset_image_unfold.lean)**

@import "lftFinset_image_unfold.lean"
**[BridgeTheorems/rhtFinset_image_unfold_mem.lean](DomainTheory/BridgeTheorems/rhtFinset_image_unfold_mem.lean)**

@import "rhtFinset_image_unfold_mem.lean"
**[BridgeTheorems/SumCon_image_treeCon.lean](DomainTheory/BridgeTheorems/SumCon_image_treeCon.lean)**

@import "SumCon_image_treeCon.lean"
**[BridgeTheorems/TreeCon_image_sumCon.lean](DomainTheory/BridgeTheorems/TreeCon_image_sumCon.lean)**

@import "TreeCon_image_sumCon.lean"
**[BridgeTheorems/TreeEnt_pairL_bot_of_pairs.lean](DomainTheory/BridgeTheorems/TreeEnt_pairL_bot_of_pairs.lean)**

@import "TreeEnt_pairL_bot_of_pairs.lean"
**[BridgeTheorems/mem_closed_pair_bots.lean](DomainTheory/BridgeTheorems/mem_closed_pair_bots.lean)**

@import "mem_closed_pair_bots.lean"
**[BridgeTheorems/saturated_of_closed.lean](DomainTheory/BridgeTheorems/saturated_of_closed.lean)**

@import "saturated_of_closed.lean"
**[BridgeTheorems/mem_foldFinset.lean](DomainTheory/BridgeTheorems/mem_foldFinset.lean)**

@import "mem_foldFinset.lean"
**[BridgeTheorems/unfoldFinset_foldFinset.lean](DomainTheory/BridgeTheorems/unfoldFinset_foldFinset.lean)**

@import "unfoldFinset_foldFinset.lean"
**[BridgeTheorems/SumEnt_treeFold.lean](DomainTheory/BridgeTheorems/SumEnt_treeFold.lean)**

@import "SumEnt_treeFold.lean"
**[BridgeTheorems/unfoldElement.lean](DomainTheory/BridgeTheorems/unfoldElement.lean)**

@import "unfoldElement.lean"
**[BridgeTheorems/TreeEnt_sumEnt.lean](DomainTheory/BridgeTheorems/TreeEnt_sumEnt.lean)**

@import "TreeEnt_sumEnt.lean"
**[BridgeTheorems/foldElement.lean](DomainTheory/BridgeTheorems/foldElement.lean)**

@import "foldElement.lean"
**[BridgeTheorems/foldElement_unfoldElement.lean](DomainTheory/BridgeTheorems/foldElement_unfoldElement.lean)**

@import "foldElement_unfoldElement.lean"
**[BridgeTheorems/unfoldElement_foldElement.lean](DomainTheory/BridgeTheorems/unfoldElement_foldElement.lean)**

@import "unfoldElement_foldElement.lean"
**[BridgeTheorems/treeDomainIso.lean](DomainTheory/BridgeTheorems/treeDomainIso.lean)**

@import "treeDomainIso.lean"
**[BridgeTheorems/SexDomainEquation.lean](DomainTheory/BridgeTheorems/SexDomainEquation.lean)**

@import "SexDomainEquation.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/idMap.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/idMap.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/idMap.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition54.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition54.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition54.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition55/comp.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition55/comp.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition55/comp.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition55.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition55.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition55.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/bar.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/bar.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/bar.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/PEnt.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/PEnt.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/PEnt.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/P.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/P.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/P.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/botElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/botElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/botElement.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/ReflApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/ReflApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/ReflApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/topElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/topElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/topElement.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/IdemApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/IdemApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/IdemApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/barElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/barElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/barElement.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/ConsistentApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/ConsistentApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/ConsistentApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/RogueApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/RogueApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/RogueApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/BotApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/BotApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/BotApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/IsDomainApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/IsDomainApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/IsDomainApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/mem_barElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/mem_barElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/mem_barElement.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/BotApprox_any.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/BotApprox_any.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/BotApprox_any.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/DomainApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/DomainApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/DomainApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/flatRel.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatRel.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/flatRel.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/mem_topElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/mem_topElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/mem_topElement.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/flatMap.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatMap.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/flatMap.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/flatDomainApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatDomainApprox.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/flatDomainApprox.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/scottCon.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/scottCon.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/scottCon.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/not_RogueApprox_idMap.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/not_RogueApprox_idMap.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/not_RogueApprox_idMap.lean"
**[InformationSystems/SomeDomainEquations/Factoid84.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/mem_botElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/mem_botElement.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/mem_botElement.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/barElement_zero_eq_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/barElement_zero_eq_bot.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/barElement_zero_eq_bot.lean"
**[InformationSystems/SomeDomainEquations/Factoid84/scottCon_empty_iff_consistent.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/scottCon_empty_iff_consistent.lean)**

@import "../InformationSystems/SomeDomainEquations/Factoid84/scottCon_empty_iff_consistent.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/constMap.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/constMap.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/constMap.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/comp_constMap.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/comp_constMap.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/comp_constMap.lean"
**[InformationSystems/ApproximableMappingsBetweenDomains/Proposition56.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition56.lean)**

@import "../InformationSystems/ApproximableMappingsBetweenDomains/Proposition56.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitSystem.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitSystem.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitSystem.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitElement_eq_bot.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitElement_eq_bot.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitElement_eq_bot.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_from_unit_eq_const.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_from_unit_eq_const.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_from_unit_eq_const.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_to_unit_eq_const.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_to_unit_eq_const.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_to_unit_eq_const.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65/toElement_constMap_bot.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/toElement_constMap_bot.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65/toElement_constMap_bot.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Factoid65.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Factoid65.lean"
**[InformationSystems/InformationSystems/lowerBoundEnt.lean](DomainTheory/InformationSystems/InformationSystems/lowerBoundEnt.lean)**

@import "../InformationSystems/InformationSystems/lowerBoundEnt.lean"
**[InformationSystems/InformationSystems/Factoid24.lean](DomainTheory/InformationSystems/InformationSystems/Factoid24.lean)**

@import "../InformationSystems/InformationSystems/Factoid24.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/mkLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/mkLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/mkLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/instLeftCommutativeMkLeftInsert.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/instLeftCommutativeMkLeftInsert.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/instLeftCommutativeMkLeftInsert.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/mkRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/mkRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/mkRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/instLeftCommutativeMkRightInsert.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/instLeftCommutativeMkRightInsert.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/instLeftCommutativeMkRightInsert.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/copair_union_disj.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copair_union_disj.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/copair_union_disj.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_lft_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_lft_of_sumEntSet.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_lft_of_sumEntSet.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_rht_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_rht_of_sumEntSet.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_rht_of_sumEntSet.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_eq_empty_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_eq_empty_of_sumEntSet.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_eq_empty_of_sumEntSet.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_mem_Con_of_SumCon_rht_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_mem_Con_of_SumCon_rht_empty.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_mem_Con_of_SumCon_rht_empty.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/not_mem_right_of_mem_left.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/not_mem_right_of_mem_left.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/not_mem_right_of_mem_left.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_eq_empty_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_eq_empty_of_sumEntSet.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_eq_empty_of_sumEntSet.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_mem_Con_of_SumCon_lft_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_mem_Con_of_SumCon_lft_empty.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_mem_Con_of_SumCon_lft_empty.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumLftCarrier.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumLftCarrier.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumLftCarrier.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementLft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementLft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementLft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumRhtCarrier.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumRhtCarrier.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumRhtCarrier.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementRht.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementRht.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementRht.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_empty.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_empty.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/entSet_fst_of_prodEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/entSet_fst_of_prodEntSet.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/entSet_fst_of_prodEntSet.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/entSet_snd_of_prodEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/entSet_snd_of_prodEntSet.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/entSet_snd_of_prodEntSet.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/liftLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/liftLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/liftLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/liftRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/liftRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/liftRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/pairMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/pairMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/pairMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/Basic.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/Basic.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/Basic.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/element_eq_of_fst_snd.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/element_eq_of_fst_snd.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/element_eq_of_fst_snd.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/mem_liftLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/mem_liftLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/mem_liftLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstFinset_liftLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstFinset_liftLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstFinset_liftLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/mem_liftRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/mem_liftRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/mem_liftRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstFinset_liftRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstFinset_liftRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstFinset_liftRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndFinset_liftLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndFinset_liftLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndFinset_liftLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndFinset_liftRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndFinset_liftRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndFinset_liftRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inl_witness.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inl_witness.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inl_witness.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inr_witness.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inr_witness.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inr_witness.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/eq_botElement_of_no_injections.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/eq_botElement_of_no_injections.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/eq_botElement_of_no_injections.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_eq_empty_or_mem.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_eq_empty_or_mem.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_eq_empty_or_mem.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_eq_empty_or_mem.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_eq_empty_or_mem.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_eq_empty_or_mem.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/subset_botElement_of_projections_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/subset_botElement_of_projections_empty.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/subset_botElement_of_projections_empty.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_empty_of_rel_bot_like.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_empty_of_rel_bot_like.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_empty_of_rel_bot_like.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftLft_of_left_only.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftLft_of_left_only.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftLft_of_left_only.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftRht_of_right_only.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftRht_of_right_only.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftRht_of_right_only.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_unique.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_unique.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_unique.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_liftLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_liftLeft.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_liftLeft.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/comp_fstMap_pairMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/comp_fstMap_pairMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/comp_fstMap_pairMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_liftRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_liftRight.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_liftRight.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/comp_sndMap_pairMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/comp_sndMap_pairMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/comp_sndMap_pairMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62/pairMap_unique.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/pairMap_unique.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62/pairMap_unique.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition62.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition62.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_comm_β.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_comm_β.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_comm_β.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_self.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_self.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_self.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/fstFinset_liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/fstFinset_liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/fstFinset_liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_input_output_union.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_input_output_union.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_input_output_union.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_approxMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_approxMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_approxMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/sndFinset_liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/sndFinset_liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/sndFinset_liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/ProdCon_liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/ProdCon_liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/ProdCon_liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/entSet_liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/entSet_liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/entSet_liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_of_funTokens.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_of_funTokens.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_of_funTokens.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_curry_pointwise.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_curry_pointwise.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_curry_pointwise.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurryMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurryMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurryMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_element_toApproxMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_element_toApproxMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_element_toApproxMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/fstMap_pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/fstMap_pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/fstMap_pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_approxMap_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_approxMap_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_approxMap_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_fst_of_subset_pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_fst_of_subset_pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_fst_of_subset_pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/sndMap_pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/sndMap_pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/sndMap_pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_snd_of_subset_pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_snd_of_subset_pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_snd_of_subset_pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftRight.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftRight.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftRight.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/theorem_7_2.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/theorem_7_2.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/theorem_7_2.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurry_curryMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurry_curryMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurry_curryMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftLeft.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftLeft.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftLeft.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftPair.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftPair.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap_unique.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap_unique.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap_unique.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72.lean"
**[BridgeTheorems/InfoSysConstructions/not_left_mem_sum_botElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/not_left_mem_sum_botElement.lean)**

@import "InfoSysConstructions/not_left_mem_sum_botElement.lean"
**[BridgeTheorems/InfoSysConstructions/lftFinset_singleton_right.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/lftFinset_singleton_right.lean)**

@import "InfoSysConstructions/lftFinset_singleton_right.lean"
**[BridgeTheorems/InfoSysConstructions/pairElements_mono.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/pairElements_mono.lean)**

@import "InfoSysConstructions/pairElements_mono.lean"
**[BridgeTheorems/InfoSysConstructions/sum_element_trichotomy.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sum_element_trichotomy.lean)**

@import "InfoSysConstructions/sum_element_trichotomy.lean"
**[BridgeTheorems/InfoSysConstructions/right_bot_mem_inrMap_toElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/right_bot_mem_inrMap_toElement.lean)**

@import "InfoSysConstructions/right_bot_mem_inrMap_toElement.lean"
**[BridgeTheorems/InfoSysConstructions/sumElementRht_inrMap_toElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sumElementRht_inrMap_toElement.lean)**

@import "InfoSysConstructions/sumElementRht_inrMap_toElement.lean"
**[BridgeTheorems/InfoSysConstructions/inrMap_toElement_le_iff.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/inrMap_toElement_le_iff.lean)**

@import "InfoSysConstructions/inrMap_toElement_le_iff.lean"
**[BridgeTheorems/InfoSysConstructions/rhtFinset_singleton_left.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/rhtFinset_singleton_left.lean)**

@import "InfoSysConstructions/rhtFinset_singleton_left.lean"
**[BridgeTheorems/InfoSysConstructions/assembleSum.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/assembleSum.lean)**

@import "InfoSysConstructions/assembleSum.lean"
**[BridgeTheorems/InfoSysConstructions/instPartialOrderApproximableMap.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/instPartialOrderApproximableMap.lean)**

@import "InfoSysConstructions/instPartialOrderApproximableMap.lean"
**[BridgeTheorems/approximableMap_scottContinuous_equiv.lean](DomainTheory/BridgeTheorems/approximableMap_scottContinuous_equiv.lean)**

@import "approximableMap_scottContinuous_equiv.lean"
**[BridgeTheorems/InfoSysConstructions/pairElements_unpair.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/pairElements_unpair.lean)**

@import "InfoSysConstructions/pairElements_unpair.lean"
**[BridgeTheorems/InfoSysConstructions/exists_assembleSum_eq.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/exists_assembleSum_eq.lean)**

@import "InfoSysConstructions/exists_assembleSum_eq.lean"
**[BridgeTheorems/InfoSysConstructions/classifySum.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/classifySum.lean)**

@import "InfoSysConstructions/classifySum.lean"
**[BridgeTheorems/InfoSysConstructions/assembleSum_classifySum.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/assembleSum_classifySum.lean)**

@import "InfoSysConstructions/assembleSum_classifySum.lean"
**[BridgeTheorems/InfoSysConstructions/assembleSum_mono.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/assembleSum_mono.lean)**

@import "InfoSysConstructions/assembleSum_mono.lean"
**[BridgeTheorems/InfoSysConstructions/unpair.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/unpair.lean)**

@import "InfoSysConstructions/unpair.lean"
**[BridgeTheorems/InfoSysConstructions/unpair_pairElements.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/unpair_pairElements.lean)**

@import "InfoSysConstructions/unpair_pairElements.lean"
**[BridgeTheorems/InfoSysConstructions/productDomainIso.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/productDomainIso.lean)**

@import "InfoSysConstructions/productDomainIso.lean"
**[BridgeTheorems/InfoSysConstructions/not_right_mem_sum_botElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/not_right_mem_sum_botElement.lean)**

@import "InfoSysConstructions/not_right_mem_sum_botElement.lean"
**[BridgeTheorems/InfoSysConstructions/approxMap_toElement_le_iff.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/approxMap_toElement_le_iff.lean)**

@import "InfoSysConstructions/approxMap_toElement_le_iff.lean"
**[BridgeTheorems/InfoSysConstructions/functionSpaceDomainIso.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/functionSpaceDomainIso.lean)**

@import "InfoSysConstructions/functionSpaceDomainIso.lean"
**[BridgeTheorems/InfoSysConstructions/left_bot_mem_inlMap_toElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/left_bot_mem_inlMap_toElement.lean)**

@import "InfoSysConstructions/left_bot_mem_inlMap_toElement.lean"
**[BridgeTheorems/InfoSysConstructions/sumElementLft_inlMap_toElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sumElementLft_inlMap_toElement.lean)**

@import "InfoSysConstructions/sumElementLft_inlMap_toElement.lean"
**[BridgeTheorems/InfoSysConstructions/inlMap_toElement_injective.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/inlMap_toElement_injective.lean)**

@import "InfoSysConstructions/inlMap_toElement_injective.lean"
**[BridgeTheorems/InfoSysConstructions/inlMap_toElement_le_iff.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/inlMap_toElement_le_iff.lean)**

@import "InfoSysConstructions/inlMap_toElement_le_iff.lean"
**[BridgeTheorems/InfoSysConstructions/inrMap_toElement_injective.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/inrMap_toElement_injective.lean)**

@import "InfoSysConstructions/inrMap_toElement_injective.lean"
**[BridgeTheorems/InfoSysConstructions/assembleSum_injective.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/assembleSum_injective.lean)**

@import "InfoSysConstructions/assembleSum_injective.lean"
**[BridgeTheorems/InfoSysConstructions/classifySum_assembleSum.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/classifySum_assembleSum.lean)**

@import "InfoSysConstructions/classifySum_assembleSum.lean"
**[BridgeTheorems/InfoSysConstructions/sumDomainIso.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sumDomainIso.lean)**

@import "InfoSysConstructions/sumDomainIso.lean"
**[BridgeTheorems/InfoSysConstructions/Basic.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/Basic.lean)**

@import "InfoSysConstructions/Basic.lean"
**[BridgeTheorems/ScottMapBridge.lean](DomainTheory/BridgeTheorems/ScottMapBridge.lean)**

@import "ScottMapBridge.lean"
**[BridgeTheorems/InfoSysConstructions/unpair_mono.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/unpair_mono.lean)**

@import "InfoSysConstructions/unpair_mono.lean"
**[BridgeTheorems/InfoSysConstructions/sumElementRht_eq.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sumElementRht_eq.lean)**

@import "InfoSysConstructions/sumElementRht_eq.lean"
**[BridgeTheorems/InfoSysConstructions/sumElementLft_eq.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sumElementLft_eq.lean)**

@import "InfoSysConstructions/sumElementLft_eq.lean"
**[BridgeTheorems/InfoSysConstructions.lean](DomainTheory/BridgeTheorems/InfoSysConstructions.lean)**

@import "InfoSysConstructions.lean"
**[BridgeTheorems/WorkedExampleSExpr/lowerBoundSystem.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/lowerBoundSystem.lean)**

@import "WorkedExampleSExpr/lowerBoundSystem.lean"
**[BridgeTheorems/WorkedExampleSExpr/SexSys.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/SexSys.lean)**

@import "WorkedExampleSExpr/SexSys.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexAtom.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexAtom.lean)**

@import "WorkedExampleSExpr/sexAtom.lean"
**[BridgeTheorems/WorkedExampleSExpr/SexRhs.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/SexRhs.lean)**

@import "WorkedExampleSExpr/SexRhs.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexRhsSemanticIso.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexRhsSemanticIso.lean)**

@import "WorkedExampleSExpr/sexRhsSemanticIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/Basic.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/Basic.lean)**

@import "WorkedExampleSExpr/Basic.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexAtom_mem_self.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexAtom_mem_self.lean)**

@import "WorkedExampleSExpr/sexAtom_mem_self.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexIdealIso.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/exists_sexIdealIso.lean)**

@import "WorkedExampleSExpr/exists_sexIdealIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexId_toElement.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexId_toElement.lean)**

@import "WorkedExampleSExpr/sexId_toElement.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_fold.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_fold.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso_fold.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_unfold.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_unfold.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso_unfold.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexDomainEquationIso.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/exists_sexDomainEquationIso.lean)**

@import "WorkedExampleSExpr/exists_sexDomainEquationIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexRhs_eq_sum_product.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexRhs_eq_sum_product.lean)**

@import "WorkedExampleSExpr/sexRhs_eq_sum_product.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexUnfold_atom.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexUnfold_atom.lean)**

@import "WorkedExampleSExpr/sexUnfold_atom.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexNeighborhoodIso.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/exists_sexNeighborhoodIso.lean)**

@import "WorkedExampleSExpr/exists_sexNeighborhoodIso.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/BoolPoint.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/BoolPoint.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/BoolPoint.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/BoolToken.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/BoolToken.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/BoolToken.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_mem_botElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_mem_botElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_mem_botElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/mem_botElement_emptyEntails.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/mem_botElement_emptyEntails.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/mem_botElement_emptyEntails.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/EmptyEntails.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/EmptyEntails.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/EmptyEntails.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_empty.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_empty.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_empty.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_funion.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_funion.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_funion.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/strictify.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/strictify.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/strictify.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictToken.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictToken.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictToken.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunToken.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunToken.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunToken.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/BasicInst22.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/BasicInst22.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/BasicInst22.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/filter_ne_subset_of_subset_insert_strict.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/filter_ne_subset_of_subset_insert_strict.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/filter_ne_subset_of_subset_insert_strict.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/insert_filter_ne_strict.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/insert_filter_ne_strict.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/insert_filter_ne_strict.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/strictBot.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/strictBot.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/strictBot.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/subset_of_entSet_mem.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/subset_of_entSet_mem.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/subset_of_entSet_mem.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/toFunFinset.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/toFunFinset.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/toFunFinset.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunCon.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunCon.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunCon.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunEnt.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunEnt.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunEnt.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/strictFunctionSystem.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/strictFunctionSystem.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/strictFunctionSystem.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/boolSat.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/boolSat.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/boolSat.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/boolSystem.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/boolSystem.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/boolSystem.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/not_ent_empty_fls.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/not_ent_empty_fls.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/not_ent_empty_fls.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/not_ent_empty_tru.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/not_ent_empty_tru.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/not_ent_empty_tru.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/boolCon_trichotomy.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/boolCon_trichotomy.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/boolCon_trichotomy.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/boolFalse.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/boolFalse.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/boolFalse.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/boolTrue.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/boolTrue.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/boolTrue.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/IsStrict.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/IsStrict.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/IsStrict.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/IsStrictToken_of_IsStrict.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/IsStrictToken_of_IsStrict.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/IsStrictToken_of_IsStrict.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/approxMap_toStrictElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/approxMap_toStrictElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/approxMap_toStrictElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/strictifyElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/strictifyElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/strictifyElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/condElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/condElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/condElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap_unique.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap_unique.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap_unique.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75/conditional_iso.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75/conditional_iso.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75/conditional_iso.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid75.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid75.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid75.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid76/compOpUncurry.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid76/compOpUncurry.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid76/compOpUncurry.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid76/constOp.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid76/constOp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid76/constOp.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid76/compOp.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid76/compOp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid76/compOp.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid76.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid76.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid76.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOpUncurry.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOpUncurry.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOpUncurry.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOp.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOp.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid76/pairMap_toElement_pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid76/pairMap_toElement_pairElements.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid76/pairMap_toElement_pairElements.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/InfoSysObj.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/InfoSysObj.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/InfoSysObj.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/unit.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/unit.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/unit.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/curry_uncurry.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/curry_uncurry.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/curry_uncurry.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/exp.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/exp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/exp.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/prod.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/prod.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/prod.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/id_acomp.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/id_acomp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/id_acomp.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/instCategoryInfoSysObj.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/instCategoryInfoSysObj.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/instCategoryInfoSysObj.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/productLimitCone.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/productLimitCone.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/productLimitCone.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/terminalLimitCone.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/terminalLimitCone.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/terminalLimitCone.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/instCartesianMonoidalCategoryInfoSysObj.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/instCartesianMonoidalCategoryInfoSysObj.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/instCartesianMonoidalCategoryInfoSysObj.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/curryProduct.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/curryProduct.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/curryProduct.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_fst_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_fst_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_fst_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_snd_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_snd_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_snd_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/pair_after_swap_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/pair_after_swap_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/pair_after_swap_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap_acomp_swapMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap_acomp_swapMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap_acomp_swapMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_fst_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_fst_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_fst_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_snd_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_snd_toElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_snd_toElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElement_eq_productElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElement_eq_productElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElement_eq_productElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/prodElementToTensorElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/prodElementToTensorElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/prodElementToTensorElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElementToProdElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElementToProdElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElementToProdElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHom_eq_productMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHom_eq_productMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHom_eq_productMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/prodHomToTensorHom.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/prodHomToTensorHom.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/prodHomToTensorHom.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHomToProdHom.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHomToProdHom.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHomToProdHom.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorMap_eq_productMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorMap_eq_productMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorMap_eq_productMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/productMapToTensorMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/productMapToTensorMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/productMapToTensorMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorLeft_map_eq.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorLeft_map_eq.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorLeft_map_eq.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryProduct.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryProduct.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryProduct.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryRight.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryRight.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryRight.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight_uncurryRight.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight_uncurryRight.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight_uncurryRight.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpEquiv.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpEquiv.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpEquiv.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpAdjunction.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpAdjunction.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpAdjunction.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/Basic.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/Basic.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/Basic.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/ihom_obj_eq_exp.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/ihom_obj_eq_exp.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/ihom_obj_eq_exp.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor_obj.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor_obj.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor_obj.lean"
**[InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorObj_eq_prod.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorObj_eq_prod.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorObj_eq_prod.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixChain.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixChain.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixChain.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixReach.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixReach.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixReach.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_con.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_con.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_con.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_empty.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_empty.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_empty.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_mono_w.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_mono_w.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_mono_w.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_pad.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_pad.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_pad.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_con.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_con.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_con.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_empty.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_empty.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_empty.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_mono_w.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_mono_w.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_mono_w.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/funEnt_union_step.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/funEnt_union_step.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/funEnt_union_step.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_union.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_union.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_union.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_union.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_union.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_union.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/Basic.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/Basic.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/Basic.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_step_of_rel.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_step_of_rel.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_step_of_rel.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_subset_pre_fixed.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_subset_pre_fixed.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_subset_pre_fixed.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_le_of_pre_fixed.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_le_of_pre_fixed.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_le_of_pre_fixed.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/toElement_fixElement_le.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/toElement_fixElement_le.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/toElement_fixElement_le.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_fixed.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_fixed.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_fixed.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_unique.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_unique.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_unique.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap_unique.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap_unique.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap_unique.lean"
**[InformationSystems/FunctionSpaceAsADomain/Fixpoint.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Fixpoint.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Fixpoint.lean"
**[InformationSystems/FunctionSpaceAsADomain/Proposition74/Basic.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Proposition74/Basic.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Proposition74/Basic.lean"
**[InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_ii.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_ii.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_ii.lean"
**[InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_unique.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_unique.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_unique.lean"
**[InformationSystems/FunctionSpaceAsADomain/Proposition74/fixChain_toElement_le_fix.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Proposition74/fixChain_toElement_le_fix.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Proposition74/fixChain_toElement_le_fix.lean"
**[InformationSystems/FunctionSpaceAsADomain/Proposition74/toElement_fix_le_fixElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Proposition74/toElement_fix_le_fixElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Proposition74/toElement_fix_le_fixElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Proposition74/toElement_comp_fix_le.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Proposition74/toElement_comp_fix_le.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Proposition74/toElement_comp_fix_le.lean"
**[InformationSystems/FunctionSpaceAsADomain/Proposition74/fixElement_le_toElement_fix.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Proposition74/fixElement_le_toElement_fix.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Proposition74/fixElement_le_toElement_fix.lean"
**[InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_iii.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_iii.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Proposition74/proposition_7_4_iii.lean"
**[InformationSystems/FunctionSpaceAsADomain/Proposition74.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Proposition74.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Proposition74.lean"
**[InformationSystems/FunctionSpaceAsADomain/Proposition74/idMap_botElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Proposition74/idMap_botElement.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Proposition74/idMap_botElement.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/liftLeft_funion.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/liftLeft_funion.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/liftLeft_funion.lean"
**[InformationSystems/FunctionSpaceAsADomain/Theorem72/liftRight_funion.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/liftRight_funion.lean)**

@import "../InformationSystems/FunctionSpaceAsADomain/Theorem72/liftRight_funion.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inlMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inlMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inlMap.lean"
**[InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inrMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inrMap.lean)**

@import "../InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inrMap.lean"
