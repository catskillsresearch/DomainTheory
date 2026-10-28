# Worked example — S-expressions / trees

**Dependencies.** Inside WorkedExampleSExpr, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. BridgeTheorems is the Lean files in that chapter folder, not in a subfolder. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "WorkedExampleSExpr/WorkedExampleSExpr.mermaid"

@import "BridgeTheorems_Worked_example.english" {code_block=false}

**[BridgeTheorems/TreeProd.lean](DomainTheory/BridgeTheorems/TreeProd.lean)**

@import "TreeProd.lean"
**[BridgeTheorems/WorkedExampleSExpr/lowerBoundSystem.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/lowerBoundSystem.lean)**

@import "WorkedExampleSExpr/lowerBoundSystem.lean"
**[BridgeTheorems/WorkedExampleSExpr/SexSys.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/SexSys.lean)**

@import "WorkedExampleSExpr/SexSys.lean"
**[BridgeTheorems/WorkedExampleSExpr/SexRhs.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/SexRhs.lean)**

@import "WorkedExampleSExpr/SexRhs.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexAtom.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexAtom.lean)**

@import "WorkedExampleSExpr/sexAtom.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexRhsSemanticIso.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexRhsSemanticIso.lean)**

@import "WorkedExampleSExpr/sexRhsSemanticIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/Basic.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/Basic.lean)**

@import "WorkedExampleSExpr/Basic.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexDomainEquationIso.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/exists_sexDomainEquationIso.lean)**

@import "WorkedExampleSExpr/exists_sexDomainEquationIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexIdealIso.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/exists_sexIdealIso.lean)**

@import "WorkedExampleSExpr/exists_sexIdealIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/exists_sexNeighborhoodIso.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/exists_sexNeighborhoodIso.lean)**

@import "WorkedExampleSExpr/exists_sexNeighborhoodIso.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexAtom_mem_self.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexAtom_mem_self.lean)**

@import "WorkedExampleSExpr/sexAtom_mem_self.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_fold.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_fold.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso_fold.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_unfold.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_unfold.lean)**

@import "WorkedExampleSExpr/sexDomainEquationIso_unfold.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexId_toElement.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexId_toElement.lean)**

@import "WorkedExampleSExpr/sexId_toElement.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexRhs_eq_sum_product.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexRhs_eq_sum_product.lean)**

@import "WorkedExampleSExpr/sexRhs_eq_sum_product.lean"
**[BridgeTheorems/WorkedExampleSExpr/sexUnfold_atom.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr/sexUnfold_atom.lean)**

@import "WorkedExampleSExpr/sexUnfold_atom.lean"
**[BridgeTheorems/treeFold.lean](DomainTheory/BridgeTheorems/treeFold.lean)**

@import "treeFold.lean"
**[BridgeTheorems/treeFold_eq_or_pairBots.lean](DomainTheory/BridgeTheorems/treeFold_eq_or_pairBots.lean)**

@import "treeFold_eq_or_pairBots.lean"
**[BridgeTheorems/treeUnfold_treeFold.lean](DomainTheory/BridgeTheorems/treeUnfold_treeFold.lean)**

@import "treeUnfold_treeFold.lean"
**[BridgeTheorems/unfoldInsert.lean](DomainTheory/BridgeTheorems/unfoldInsert.lean)**

@import "unfoldInsert.lean"
**[BridgeTheorems/SexDomainEquationInst10.lean](DomainTheory/BridgeTheorems/SexDomainEquationInst10.lean)**

@import "SexDomainEquationInst10.lean"
**[BridgeTheorems/foldInsert.lean](DomainTheory/BridgeTheorems/foldInsert.lean)**

@import "foldInsert.lean"
**[BridgeTheorems/SexDomainEquationInst15.lean](DomainTheory/BridgeTheorems/SexDomainEquationInst15.lean)**

@import "SexDomainEquationInst15.lean"
**[BridgeTheorems/TreeEnt_pairL_bot_of_pairs.lean](DomainTheory/BridgeTheorems/TreeEnt_pairL_bot_of_pairs.lean)**

@import "TreeEnt_pairL_bot_of_pairs.lean"
**[BridgeTheorems/TreeEnt_pairR_bot_of_pairs.lean](DomainTheory/BridgeTheorems/TreeEnt_pairR_bot_of_pairs.lean)**

@import "TreeEnt_pairR_bot_of_pairs.lean"
**[BridgeTheorems/foldFinset.lean](DomainTheory/BridgeTheorems/foldFinset.lean)**

@import "foldFinset.lean"
**[BridgeTheorems/mem_closed_pair_bots.lean](DomainTheory/BridgeTheorems/mem_closed_pair_bots.lean)**

@import "mem_closed_pair_bots.lean"
**[BridgeTheorems/saturated_of_closed.lean](DomainTheory/BridgeTheorems/saturated_of_closed.lean)**

@import "saturated_of_closed.lean"
**[BridgeTheorems/mem_foldr_fold.lean](DomainTheory/BridgeTheorems/mem_foldr_fold.lean)**

@import "mem_foldr_fold.lean"
**[BridgeTheorems/mem_foldFinset.lean](DomainTheory/BridgeTheorems/mem_foldFinset.lean)**

@import "mem_foldFinset.lean"
**[BridgeTheorems/mem_foldr_unfold.lean](DomainTheory/BridgeTheorems/mem_foldr_unfold.lean)**

@import "mem_foldr_unfold.lean"
**[BridgeTheorems/unfoldFinset.lean](DomainTheory/BridgeTheorems/unfoldFinset.lean)**

@import "unfoldFinset.lean"
**[BridgeTheorems/mem_unfoldFinset.lean](DomainTheory/BridgeTheorems/mem_unfoldFinset.lean)**

@import "mem_unfoldFinset.lean"
**[BridgeTheorems/lftFinset_image_unfold.lean](DomainTheory/BridgeTheorems/lftFinset_image_unfold.lean)**

@import "lftFinset_image_unfold.lean"
**[BridgeTheorems/rhtFinset_image_unfold_mem.lean](DomainTheory/BridgeTheorems/rhtFinset_image_unfold_mem.lean)**

@import "rhtFinset_image_unfold_mem.lean"
**[BridgeTheorems/SumCon_image_treeCon.lean](DomainTheory/BridgeTheorems/SumCon_image_treeCon.lean)**

@import "SumCon_image_treeCon.lean"
**[BridgeTheorems/SumEnt_treeFold.lean](DomainTheory/BridgeTheorems/SumEnt_treeFold.lean)**

@import "SumEnt_treeFold.lean"
**[BridgeTheorems/TreeCon_image_sumCon.lean](DomainTheory/BridgeTheorems/TreeCon_image_sumCon.lean)**

@import "TreeCon_image_sumCon.lean"
**[BridgeTheorems/TreeEnt_sumEnt.lean](DomainTheory/BridgeTheorems/TreeEnt_sumEnt.lean)**

@import "TreeEnt_sumEnt.lean"
**[BridgeTheorems/foldElement.lean](DomainTheory/BridgeTheorems/foldElement.lean)**

@import "foldElement.lean"
**[BridgeTheorems/unfoldFinset_foldFinset.lean](DomainTheory/BridgeTheorems/unfoldFinset_foldFinset.lean)**

@import "unfoldFinset_foldFinset.lean"
**[BridgeTheorems/unfoldElement.lean](DomainTheory/BridgeTheorems/unfoldElement.lean)**

@import "unfoldElement.lean"
**[BridgeTheorems/foldElement_unfoldElement.lean](DomainTheory/BridgeTheorems/foldElement_unfoldElement.lean)**

@import "foldElement_unfoldElement.lean"
**[BridgeTheorems/unfoldElement_foldElement.lean](DomainTheory/BridgeTheorems/unfoldElement_foldElement.lean)**

@import "unfoldElement_foldElement.lean"
**[BridgeTheorems/treeDomainIso.lean](DomainTheory/BridgeTheorems/treeDomainIso.lean)**

@import "treeDomainIso.lean"
**[BridgeTheorems/SexDomainEquation.lean](DomainTheory/BridgeTheorems/SexDomainEquation.lean)**

@import "SexDomainEquation.lean"
