# Worked example — S-expressions / trees

**Dependencies.** Inside WorkedExampleSExpr, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. BridgeTheorems is the Lean files in that chapter folder, not in a subfolder. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "WorkedExampleSExpr/WorkedExampleSExpr.mermaid"

@import "BridgeTheorems_Worked_example.english" {code_block=false}

**[BridgeTheorems/TreeProd.lean](TreeProd.lean)**

@import "TreeProd.lean"
**[BridgeTheorems/WorkedExampleSExpr/lowerBoundSystem.lean](WorkedExampleSExpr/lowerBoundSystem.lean)**

@import "WorkedExampleSExpr/lowerBoundSystem.lean"
**[BridgeTheorems/WorkedExampleSExpr/SexSys.lean](WorkedExampleSExpr/SexSys.lean)**

@import "WorkedExampleSExpr/SexSys.lean"
**[BridgeTheorems/WorkedExampleSExpr/SexRhs.lean](WorkedExampleSExpr/SexRhs.lean)**

@import "WorkedExampleSExpr/SexRhs.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexAtom.lean](WorkedExampleSExpr/sexAtom.lean)**

@import "WorkedExampleSExpr/sexAtom.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso.lean](WorkedExampleSExpr/sexDomainEquationIso.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexRhsSemanticIso.lean](WorkedExampleSExpr/sexRhsSemanticIso.lean)**

@import "WorkedExampleSExpr/sexRhsSemanticIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/Basic.lean](WorkedExampleSExpr/Basic.lean)**

@import "WorkedExampleSExpr/Basic.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexDomainEquationIso.lean](WorkedExampleSExpr/exists_sexDomainEquationIso.lean)**

@import "WorkedExampleSExpr/exists_sexDomainEquationIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexIdealIso.lean](WorkedExampleSExpr/exists_sexIdealIso.lean)**

@import "WorkedExampleSExpr/exists_sexIdealIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexNeighborhoodIso.lean](WorkedExampleSExpr/exists_sexNeighborhoodIso.lean)**

@import "WorkedExampleSExpr/exists_sexNeighborhoodIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexAtom_mem_self.lean](WorkedExampleSExpr/sexAtom_mem_self.lean)**

@import "WorkedExampleSExpr/sexAtom_mem_self.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_fold.lean](WorkedExampleSExpr/sexDomainEquationIso_fold.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso_fold.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_unfold.lean](WorkedExampleSExpr/sexDomainEquationIso_unfold.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso_unfold.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexId_toElement.lean](WorkedExampleSExpr/sexId_toElement.lean)**

@import "WorkedExampleSExpr/sexId_toElement.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexRhs_eq_sum_product.lean](WorkedExampleSExpr/sexRhs_eq_sum_product.lean)**

@import "WorkedExampleSExpr/sexRhs_eq_sum_product.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexUnfold_atom.lean](WorkedExampleSExpr/sexUnfold_atom.lean)**

@import "WorkedExampleSExpr/sexUnfold_atom.lean"
**[BridgeTheorems/WorkedExampleSExpr.lean](WorkedExampleSExpr.lean)**

@import "WorkedExampleSExpr.lean"
**[BridgeTheorems/treeFold.lean](treeFold.lean)**

@import "treeFold.lean"
**[BridgeTheorems/treeFold_eq_or_pairBots.lean](treeFold_eq_or_pairBots.lean)**

@import "treeFold_eq_or_pairBots.lean"
**[BridgeTheorems/treeUnfold_treeFold.lean](treeUnfold_treeFold.lean)**

@import "treeUnfold_treeFold.lean"
**[BridgeTheorems/unfoldInsert.lean](unfoldInsert.lean)**

@import "unfoldInsert.lean"
**[BridgeTheorems/SexDomainEquationInst10.lean](SexDomainEquationInst10.lean)**

@import "SexDomainEquationInst10.lean"
**[BridgeTheorems/foldInsert.lean](foldInsert.lean)**

@import "foldInsert.lean"
**[BridgeTheorems/SexDomainEquationInst15.lean](SexDomainEquationInst15.lean)**

@import "SexDomainEquationInst15.lean"
**[BridgeTheorems/TreeEnt_pairL_bot_of_pairs.lean](TreeEnt_pairL_bot_of_pairs.lean)**

@import "TreeEnt_pairL_bot_of_pairs.lean"
**[BridgeTheorems/TreeEnt_pairR_bot_of_pairs.lean](TreeEnt_pairR_bot_of_pairs.lean)**

@import "TreeEnt_pairR_bot_of_pairs.lean"
**[BridgeTheorems/foldFinset.lean](foldFinset.lean)**

@import "foldFinset.lean"
**[BridgeTheorems/mem_closed_pair_bots.lean](mem_closed_pair_bots.lean)**

@import "mem_closed_pair_bots.lean"
**[BridgeTheorems/saturated_of_closed.lean](saturated_of_closed.lean)**

@import "saturated_of_closed.lean"
**[BridgeTheorems/mem_foldr_fold.lean](mem_foldr_fold.lean)**

@import "mem_foldr_fold.lean"
**[BridgeTheorems/mem_foldFinset.lean](mem_foldFinset.lean)**

@import "mem_foldFinset.lean"
**[BridgeTheorems/mem_foldr_unfold.lean](mem_foldr_unfold.lean)**

@import "mem_foldr_unfold.lean"
**[BridgeTheorems/unfoldFinset.lean](unfoldFinset.lean)**

@import "unfoldFinset.lean"
**[BridgeTheorems/mem_unfoldFinset.lean](mem_unfoldFinset.lean)**

@import "mem_unfoldFinset.lean"
**[BridgeTheorems/lftFinset_image_unfold.lean](lftFinset_image_unfold.lean)**

@import "lftFinset_image_unfold.lean"
**[BridgeTheorems/rhtFinset_image_unfold_mem.lean](rhtFinset_image_unfold_mem.lean)**

@import "rhtFinset_image_unfold_mem.lean"
**[BridgeTheorems/SumCon_image_treeCon.lean](SumCon_image_treeCon.lean)**

@import "SumCon_image_treeCon.lean"
**[BridgeTheorems/SumEnt_treeFold.lean](SumEnt_treeFold.lean)**

@import "SumEnt_treeFold.lean"
**[BridgeTheorems/TreeCon_image_sumCon.lean](TreeCon_image_sumCon.lean)**

@import "TreeCon_image_sumCon.lean"
**[BridgeTheorems/TreeEnt_sumEnt.lean](TreeEnt_sumEnt.lean)**

@import "TreeEnt_sumEnt.lean"
**[BridgeTheorems/foldElement.lean](foldElement.lean)**

@import "foldElement.lean"
**[BridgeTheorems/unfoldFinset_foldFinset.lean](unfoldFinset_foldFinset.lean)**

@import "unfoldFinset_foldFinset.lean"
**[BridgeTheorems/unfoldElement.lean](unfoldElement.lean)**

@import "unfoldElement.lean"
**[BridgeTheorems/foldElement_unfoldElement.lean](foldElement_unfoldElement.lean)**

@import "foldElement_unfoldElement.lean"
**[BridgeTheorems/unfoldElement_foldElement.lean](unfoldElement_foldElement.lean)**

@import "unfoldElement_foldElement.lean"
**[BridgeTheorems/treeDomainIso.lean](treeDomainIso.lean)**

@import "treeDomainIso.lean"
**[BridgeTheorems/SexDomainEquation.lean](SexDomainEquation.lean)**

@import "SexDomainEquation.lean"
