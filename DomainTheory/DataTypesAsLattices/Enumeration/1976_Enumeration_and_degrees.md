# Enumeration and degrees

**Historical note.** Reduction to a few combinators is old in combinatory logic. The device special to this model is (3.1), which folds the arithmetical combinators into the one combinator $\mathbf{G}$. The Gödel numbering and the second recursion theorem are the standard constructions, written so that arithmetic and the type-free combinators share a notation, and the incompleteness theorem is the standard one in that notation. Theorem 3.5 is the argument of Myhill and Shepherdson (1955); Martin Hyland pointed out the connection. Theorem 3.6 restates enumeration degrees, as in Rogers (1967), Sasso (1975), and Gutteridge (1971). Scott notes that this area was underdeveloped beside the theory of Turing degrees. Semigroups of combinators had been discussed by Church and by Böhm, and Theorem 3.7 reads that discussion inside $\mathbf{RE} \cap \mathbf{FUN}$.

**Dependencies.** Inside Enumeration, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Enumeration.mermaid"

@import "1976_Enumeration_and_degrees.english" {code_block=false}

**[DataTypesAsLattices/Enumeration/seq2_left_isScottContinuous.lean](seq2_left_isScottContinuous.lean)**

@import "seq2_left_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/opNat.lean](opNat.lean)**

@import "opNat.lean"
**[DataTypesAsLattices/Enumeration/REPredu2eexists_param.lean](REPredu2eexists_param.lean)**

@import "REPredu2eexists_param.lean"
**[DataTypesAsLattices/Enumeration/TOT.lean](TOT.lean)**

@import "TOT.lean"
**[DataTypesAsLattices/Enumeration/secondRecSubst.lean](secondRecSubst.lean)**

@import "secondRecSubst.lean"
**[DataTypesAsLattices/Enumeration/seq2_right_isScottContinuous.lean](seq2_right_isScottContinuous.lean)**

@import "seq2_right_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/eq_3_2.lean](eq_3_2.lean)**

@import "eq_3_2.lean"
**[DataTypesAsLattices/Enumeration/seqCons_right_isScottContinuous.lean](seqCons_right_isScottContinuous.lean)**

@import "seqCons_right_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/bitList.lean](bitList.lean)**

@import "bitList.lean"
**[DataTypesAsLattices/Enumeration/e_subset_ofNat_iff.lean](e_subset_ofNat_iff.lean)**

@import "e_subset_ofNat_iff.lean"
**[DataTypesAsLattices/Enumeration/unpairWRec.lean](unpairWRec.lean)**

@import "unpairWRec.lean"
**[DataTypesAsLattices/Enumeration/exists_triangle_succ.lean](exists_triangle_succ.lean)**

@import "exists_triangle_succ.lean"
**[DataTypesAsLattices/Enumeration/unpairComp.lean](unpairComp.lean)**

@import "unpairComp.lean"
**[DataTypesAsLattices/Enumeration/barPos.lean](barPos.lean)**

@import "barPos.lean"
**[DataTypesAsLattices/Enumeration/barStepBody.lean](barStepBody.lean)**

@import "barStepBody.lean"
**[DataTypesAsLattices/Enumeration/barStep.lean](barStep.lean)**

@import "barStep.lean"
**[DataTypesAsLattices/Enumeration/seq2_eq_SK.lean](seq2_eq_SK.lean)**

@import "seq2_eq_SK.lean"
**[DataTypesAsLattices/Enumeration/enumerationUnion_right_isScottContinuous.lean](enumerationUnion_right_isScottContinuous.lean)**

@import "enumerationUnion_right_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/Extensional.lean](Extensional.lean)**

@import "Extensional.lean"
**[DataTypesAsLattices/Enumeration/eq_3_8_apply.lean](eq_3_8_apply.lean)**

@import "eq_3_8_apply.lean"
**[DataTypesAsLattices/Enumeration/sucClosed.lean](sucClosed.lean)**

@import "sucClosed.lean"
**[DataTypesAsLattices/Enumeration/mem_funOf_ofNat.lean](mem_funOf_ofNat.lean)**

@import "mem_funOf_ofNat.lean"
**[DataTypesAsLattices/Enumeration/kClosed.lean](kClosed.lean)**

@import "kClosed.lean"
**[DataTypesAsLattices/Enumeration/valStepValue.lean](valStepValue.lean)**

@import "valStepValue.lean"
**[DataTypesAsLattices/Enumeration/sClosed.lean](sClosed.lean)**

@import "sClosed.lean"
**[DataTypesAsLattices/Enumeration/argNat.lean](argNat.lean)**

@import "argNat.lean"
**[DataTypesAsLattices/Enumeration/interStepTerm.lean](interStepTerm.lean)**

@import "interStepTerm.lean"
**[DataTypesAsLattices/Enumeration/interC_combinatory.lean](interC_combinatory.lean)**

@import "interC_combinatory.lean"
**[DataTypesAsLattices/Enumeration/union_combinatory.lean](union_combinatory.lean)**

@import "union_combinatory.lean"
**[DataTypesAsLattices/Enumeration/unionBits.lean](unionBits.lean)**

@import "unionBits.lean"
**[DataTypesAsLattices/Enumeration/enumBottomTerm.lean](enumBottomTerm.lean)**

@import "enumBottomTerm.lean"
**[DataTypesAsLattices/Enumeration/valRank.lean](valRank.lean)**

@import "valRank.lean"
**[DataTypesAsLattices/Enumeration/funRetractTerm.lean](funRetractTerm.lean)**

@import "funRetractTerm.lean"
**[DataTypesAsLattices/Enumeration/funRetract_combinatory.lean](funRetract_combinatory.lean)**

@import "funRetract_combinatory.lean"
**[DataTypesAsLattices/Enumeration/graph_mem_FUN.lean](graph_mem_FUN.lean)**

@import "graph_mem_FUN.lean"
**[DataTypesAsLattices/Enumeration/enumComp.lean](enumComp.lean)**

@import "enumComp.lean"
**[DataTypesAsLattices/Enumeration/Rcomb.lean](Rcomb.lean)**

@import "Rcomb.lean"
**[DataTypesAsLattices/Enumeration/unpairW.lean](unpairW.lean)**

@import "unpairW.lean"
**[DataTypesAsLattices/Enumeration/primrec_applyNat.lean](primrec_applyNat.lean)**

@import "primrec_applyNat.lean"
**[DataTypesAsLattices/Enumeration/eq_3_9_apply.lean](eq_3_9_apply.lean)**

@import "eq_3_9_apply.lean"
**[DataTypesAsLattices/Enumeration/seq2_combinatory.lean](seq2_combinatory.lean)**

@import "seq2_combinatory.lean"
**[DataTypesAsLattices/Enumeration/Gpack.lean](Gpack.lean)**

@import "Gpack.lean"
**[DataTypesAsLattices/Enumeration/Gcomb.lean](Gcomb.lean)**

@import "Gcomb.lean"
**[DataTypesAsLattices/Enumeration/not_mem_zero_Gcomb.lean](not_mem_zero_Gcomb.lean)**

@import "not_mem_zero_Gcomb.lean"
**[DataTypesAsLattices/Enumeration/valStep.lean](valStep.lean)**

@import "valStep.lean"
**[DataTypesAsLattices/Enumeration/Subalgebra.lean](Subalgebra.lean)**

@import "Subalgebra.lean"
**[DataTypesAsLattices/Enumeration/vaalF.lean](vaalF.lean)**

@import "vaalF.lean"
**[DataTypesAsLattices/Enumeration/GeneratedSubalgebra.lean](GeneratedSubalgebra.lean)**

@import "GeneratedSubalgebra.lean"
**[DataTypesAsLattices/Enumeration/enumerationUnion_left_isScottContinuous.lean](enumerationUnion_left_isScottContinuous.lean)**

@import "enumerationUnion_left_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/unionOperator_app.lean](unionOperator_app.lean)**

@import "unionOperator_app.lean"
**[DataTypesAsLattices/Functionality/treeF_isScottContinuous.lean](../Functionality/treeF_isScottContinuous.lean)**

@import "../Functionality/treeF_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/treeR_isRetract.lean](../Functionality/treeR_isRetract.lean)**

@import "../Functionality/treeR_isRetract.lean"
**[DataTypesAsLattices/Functionality/eq_4_38.lean](../Functionality/eq_4_38.lean)**

@import "../Functionality/eq_4_38.lean"
**[DataTypesAsLattices/Enumeration/predClosed.lean](predClosed.lean)**

@import "predClosed.lean"
**[DataTypesAsLattices/Enumeration/condClosed.lean](condClosed.lean)**

@import "condClosed.lean"
**[DataTypesAsLattices/Enumeration/interp_avoids.lean](interp_avoids.lean)**

@import "interp_avoids.lean"
**[DataTypesAsLattices/Enumeration/seqConsTerm.lean](seqConsTerm.lean)**

@import "seqConsTerm.lean"
**[DataTypesAsLattices/Enumeration/seq2Term.lean](seq2Term.lean)**

@import "seq2Term.lean"
**[DataTypesAsLattices/Enumeration/barPosTerm.lean](barPosTerm.lean)**

@import "barPosTerm.lean"
**[DataTypesAsLattices/Enumeration/Rterm.lean](Rterm.lean)**

@import "Rterm.lean"
**[DataTypesAsLattices/Enumeration/Rcomb_more.lean](Rcomb_more.lean)**

@import "Rcomb_more.lean"
**[DataTypesAsLattices/Enumeration/gpackClosed.lean](gpackClosed.lean)**

@import "gpackClosed.lean"
**[DataTypesAsLattices/Enumeration/gClosed.lean](gClosed.lean)**

@import "gClosed.lean"
**[DataTypesAsLattices/Enumeration/vaalStepTerm.lean](vaalStepTerm.lean)**

@import "vaalStepTerm.lean"
**[DataTypesAsLattices/Enumeration/barStepTerm.lean](barStepTerm.lean)**

@import "barStepTerm.lean"
**[DataTypesAsLattices/Enumeration/vaalC.lean](vaalC.lean)**

@import "vaalC.lean"
**[DataTypesAsLattices/Enumeration/vaalTyped.lean](vaalTyped.lean)**

@import "vaalTyped.lean"
**[DataTypesAsLattices/Enumeration/barComb.lean](barComb.lean)**

@import "barComb.lean"
**[DataTypesAsLattices/Enumeration/eq_3_15.lean](eq_3_15.lean)**

@import "eq_3_15.lean"
**[DataTypesAsLattices/Enumeration/barComb_more.lean](barComb_more.lean)**

@import "barComb_more.lean"
**[DataTypesAsLattices/Enumeration/condC_app2.lean](condC_app2.lean)**

@import "condC_app2.lean"
**[DataTypesAsLattices/Enumeration/not_mem_zero_cond_graph.lean](not_mem_zero_cond_graph.lean)**

@import "not_mem_zero_cond_graph.lean"
**[DataTypesAsLattices/Enumeration/cond_graph_eq_bot_iff.lean](cond_graph_eq_bot_iff.lean)**

@import "cond_graph_eq_bot_iff.lean"
**[DataTypesAsLattices/Enumeration/eq_3_1.lean](eq_3_1.lean)**

@import "eq_3_1.lean"
**[DataTypesAsLattices/Enumeration/eq_3_10_apply.lean](eq_3_10_apply.lean)**

@import "eq_3_10_apply.lean"
**[DataTypesAsLattices/Enumeration/GeneratedFromG.lean](GeneratedFromG.lean)**

@import "GeneratedFromG.lean"
**[DataTypesAsLattices/Enumeration/primrec_num.lean](primrec_num.lean)**

@import "primrec_num.lean"
**[DataTypesAsLattices/Enumeration/primrec_secondRecSubst.lean](primrec_secondRecSubst.lean)**

@import "primrec_secondRecSubst.lean"
**[DataTypesAsLattices/Enumeration/secondRecSubstC.lean](secondRecSubstC.lean)**

@import "secondRecSubstC.lean"
**[DataTypesAsLattices/Enumeration/Icomb_SK.lean](Icomb_SK.lean)**

@import "Icomb_SK.lean"
**[DataTypesAsLattices/Enumeration/recNat.lean](recNat.lean)**

@import "recNat.lean"
**[DataTypesAsLattices/Enumeration/primrec_recNat.lean](primrec_recNat.lean)**

@import "primrec_recNat.lean"
**[DataTypesAsLattices/Enumeration/secondRecVal.lean](secondRecVal.lean)**

@import "secondRecVal.lean"
**[DataTypesAsLattices/Enumeration/secondRecOperator.lean](secondRecOperator.lean)**

@import "secondRecOperator.lean"
**[DataTypesAsLattices/Enumeration/funOf_ofNat_mem_re.lean](funOf_ofNat_mem_re.lean)**

@import "funOf_ofNat_mem_re.lean"
**[DataTypesAsLattices/Enumeration/primrec_triangle.lean](primrec_triangle.lean)**

@import "primrec_triangle.lean"
**[DataTypesAsLattices/Enumeration/primrec_unpairW.lean](primrec_unpairW.lean)**

@import "primrec_unpairW.lean"
**[DataTypesAsLattices/Enumeration/primrec_unpairComp.lean](primrec_unpairComp.lean)**

@import "primrec_unpairComp.lean"
**[DataTypesAsLattices/Enumeration/eq_3_5.lean](eq_3_5.lean)**

@import "eq_3_5.lean"
**[DataTypesAsLattices/Enumeration/eq_3_6.lean](eq_3_6.lean)**

@import "eq_3_6.lean"
**[DataTypesAsLattices/Enumeration/Lcomb.lean](Lcomb.lean)**

@import "Lcomb.lean"
**[DataTypesAsLattices/Enumeration/Gcomb_more.lean](Gcomb_more.lean)**

@import "Gcomb_more.lean"
**[DataTypesAsLattices/Enumeration/Deg.lean](Deg.lean)**

@import "Deg.lean"
**[DataTypesAsLattices/Enumeration/Kcomb_from_G.lean](Kcomb_from_G.lean)**

@import "Kcomb_from_G.lean"
**[DataTypesAsLattices/Enumeration/condC_from_G.lean](condC_from_G.lean)**

@import "condC_from_G.lean"
**[DataTypesAsLattices/Enumeration/Scomb_from_G.lean](Scomb_from_G.lean)**

@import "Scomb_from_G.lean"
**[DataTypesAsLattices/Enumeration/predC_from_G.lean](predC_from_G.lean)**

@import "predC_from_G.lean"
**[DataTypesAsLattices/Enumeration/Gbar.lean](Gbar.lean)**

@import "Gbar.lean"
**[DataTypesAsLattices/Enumeration/GeneratedSemigroup.lean](GeneratedSemigroup.lean)**

@import "GeneratedSemigroup.lean"
**[DataTypesAsLattices/Enumeration/Lterm.lean](Lterm.lean)**

@import "Lterm.lean"
**[DataTypesAsLattices/Enumeration/Lterm_more.lean](Lterm_more.lean)**

@import "Lterm_more.lean"
**[DataTypesAsLattices/Enumeration/haltEnum.lean](haltEnum.lean)**

@import "haltEnum.lean"
**[DataTypesAsLattices/Enumeration/primrec_haltEnum.lean](primrec_haltEnum.lean)**

@import "primrec_haltEnum.lean"
**[DataTypesAsLattices/Enumeration/haltEnum_more.lean](haltEnum_more.lean)**

@import "haltEnum_more.lean"
**[DataTypesAsLattices/Enumeration/beforeHalt.lean](beforeHalt.lean)**

@import "beforeHalt.lean"
**[DataTypesAsLattices/Enumeration/BasicInst85.lean](BasicInst85.lean)**

@import "BasicInst85.lean"
**[DataTypesAsLattices/Enumeration/filterNum.lean](filterNum.lean)**

@import "filterNum.lean"
**[DataTypesAsLattices/Enumeration/primrecPred_beforeHalt.lean](primrecPred_beforeHalt.lean)**

@import "primrecPred_beforeHalt.lean"
**[DataTypesAsLattices/Enumeration/primrec_filterNum.lean](primrec_filterNum.lean)**

@import "primrec_filterNum.lean"
**[DataTypesAsLattices/Enumeration/filterRealizer.lean](filterRealizer.lean)**

@import "filterRealizer.lean"
**[DataTypesAsLattices/Enumeration/filterEnv.lean](filterEnv.lean)**

@import "filterEnv.lean"
**[DataTypesAsLattices/Enumeration/filterSeq_isScottContinuous.lean](filterSeq_isScottContinuous.lean)**

@import "filterSeq_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/filterTerm.lean](filterTerm.lean)**

@import "filterTerm.lean"
**[DataTypesAsLattices/Enumeration/filterC.lean](filterC.lean)**

@import "filterC.lean"
**[DataTypesAsLattices/Enumeration/sucC_from_G.lean](sucC_from_G.lean)**

@import "sucC_from_G.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_1.lean](theorem_3_1.lean)**

@import "theorem_3_1.lean"
**[DataTypesAsLattices/Enumeration/combinatory_mem_Deg.lean](combinatory_mem_Deg.lean)**

@import "combinatory_mem_Deg.lean"
**[DataTypesAsLattices/Enumeration/combinatory_mem_subalgebra.lean](combinatory_mem_subalgebra.lean)**

@import "combinatory_mem_subalgebra.lean"
**[DataTypesAsLattices/Enumeration/seq2_mem_subalgebra.lean](seq2_mem_subalgebra.lean)**

@import "seq2_mem_subalgebra.lean"
**[DataTypesAsLattices/Enumeration/packList.lean](packList.lean)**

@import "packList.lean"
**[DataTypesAsLattices/Enumeration/singleGenerator.lean](singleGenerator.lean)**

@import "singleGenerator.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_6.lean](theorem_3_6.lean)**

@import "theorem_3_6.lean"
**[DataTypesAsLattices/Enumeration/generators_mem_singleGenerator_degree.lean](generators_mem_singleGenerator_degree.lean)**

@import "generators_mem_singleGenerator_degree.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_6_more.lean](theorem_3_6_more.lean)**

@import "theorem_3_6_more.lean"
**[DataTypesAsLattices/Enumeration/valNat.lean](valNat.lean)**

@import "valNat.lean"
**[DataTypesAsLattices/Enumeration/eq_3_8_val.lean](eq_3_8_val.lean)**

@import "eq_3_8_val.lean"
**[DataTypesAsLattices/Enumeration/eq_3_9_val.lean](eq_3_9_val.lean)**

@import "eq_3_9_val.lean"
**[DataTypesAsLattices/Enumeration/eq_3_10_val.lean](eq_3_10_val.lean)**

@import "eq_3_10_val.lean"
**[DataTypesAsLattices/Enumeration/valStage_subset.lean](valStage_subset.lean)**

@import "valStage_subset.lean"
**[DataTypesAsLattices/Enumeration/valStage_eq_of_rank_le.lean](valStage_eq_of_rank_le.lean)**

@import "valStage_eq_of_rank_le.lean"
**[DataTypesAsLattices/Enumeration/eq_3_12.lean](eq_3_12.lean)**

@import "eq_3_12.lean"
**[DataTypesAsLattices/Enumeration/ValTrace.lean](ValTrace.lean)**

@import "ValTrace.lean"
**[DataTypesAsLattices/Enumeration/valTraceG.lean](valTraceG.lean)**

@import "valTraceG.lean"
**[DataTypesAsLattices/Enumeration/valTraceHas.lean](valTraceHas.lean)**

@import "valTraceHas.lean"
**[DataTypesAsLattices/Enumeration/primrecRel_valTraceHas.lean](primrecRel_valTraceHas.lean)**

@import "primrecRel_valTraceHas.lean"
**[DataTypesAsLattices/Enumeration/valEntryJustified.lean](valEntryJustified.lean)**

@import "valEntryJustified.lean"
**[DataTypesAsLattices/Enumeration/primrecPred_valEntryJustified.lean](primrecPred_valEntryJustified.lean)**

@import "primrecPred_valEntryJustified.lean"
**[DataTypesAsLattices/Enumeration/valTraceStruct.lean](valTraceStruct.lean)**

@import "valTraceStruct.lean"
**[DataTypesAsLattices/Enumeration/primrecPred_valTraceStruct.lean](primrecPred_valTraceStruct.lean)**

@import "primrecPred_valTraceStruct.lean"
**[DataTypesAsLattices/Enumeration/realizes_valNat_mem.lean](realizes_valNat_mem.lean)**

@import "realizes_valNat_mem.lean"
**[DataTypesAsLattices/Enumeration/Lcomb_more.lean](Lcomb_more.lean)**

@import "Lcomb_more.lean"
**[DataTypesAsLattices/Enumeration/eq_3_16.lean](eq_3_16.lean)**

@import "eq_3_16.lean"
**[DataTypesAsLattices/Enumeration/eq_3_17.lean](eq_3_17.lean)**

@import "eq_3_17.lean"
**[DataTypesAsLattices/Enumeration/bar_generated.lean](bar_generated.lean)**

@import "bar_generated.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_2.lean](theorem_3_2.lean)**

@import "theorem_3_2.lean"
**[DataTypesAsLattices/Enumeration/interCode.lean](interCode.lean)**

@import "interCode.lean"
**[DataTypesAsLattices/Enumeration/diagonalInterCode.lean](diagonalInterCode.lean)**

@import "diagonalInterCode.lean"
**[DataTypesAsLattices/Enumeration/primrec_diagonalInterCode.lean](primrec_diagonalInterCode.lean)**

@import "primrec_diagonalInterCode.lean"
**[DataTypesAsLattices/Enumeration/botCode.lean](botCode.lean)**

@import "botCode.lean"
**[DataTypesAsLattices/Enumeration/secondRecOperatorCode.lean](secondRecOperatorCode.lean)**

@import "secondRecOperatorCode.lean"
**[DataTypesAsLattices/Enumeration/Ycode.lean](Ycode.lean)**

@import "Ycode.lean"
**[DataTypesAsLattices/Enumeration/secondRecV.lean](secondRecV.lean)**

@import "secondRecV.lean"
**[DataTypesAsLattices/Enumeration/primrec_secondRecV.lean](primrec_secondRecV.lean)**

@import "primrec_secondRecV.lean"
**[DataTypesAsLattices/Enumeration/recCode.lean](recCode.lean)**

@import "recCode.lean"
**[DataTypesAsLattices/Enumeration/unionCode.lean](unionCode.lean)**

@import "unionCode.lean"
**[DataTypesAsLattices/Enumeration/finAux.lean](finAux.lean)**

@import "finAux.lean"
**[DataTypesAsLattices/Enumeration/fin.lean](fin.lean)**

@import "fin.lean"
**[DataTypesAsLattices/Enumeration/primrecu2082_finAux.lean](primrecu2082_finAux.lean)**

@import "primrecu2082_finAux.lean"
**[DataTypesAsLattices/Computability/theorem_2_6.lean](../Computability/theorem_2_6.lean)**

@import "../Computability/theorem_2_6.lean"
**[DataTypesAsLattices/Enumeration/myhillQ.lean](myhillQ.lean)**

@import "myhillQ.lean"
**[DataTypesAsLattices/Enumeration/mem_myhillQ.lean](mem_myhillQ.lean)**

@import "mem_myhillQ.lean"
**[DataTypesAsLattices/Enumeration/primrec_fin.lean](primrec_fin.lean)**

@import "primrec_fin.lean"
**[DataTypesAsLattices/Enumeration/generatedSemigroup_mem_RE_FUN.lean](generatedSemigroup_mem_RE_FUN.lean)**

@import "generatedSemigroup_mem_RE_FUN.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_7.lean](theorem_3_7.lean)**

@import "theorem_3_7.lean"
**[DataTypesAsLattices/Enumeration/valTraceOk.lean](valTraceOk.lean)**

@import "valTraceOk.lean"
**[DataTypesAsLattices/Enumeration/exists_concat_traces.lean](exists_concat_traces.lean)**

@import "exists_concat_traces.lean"
**[DataTypesAsLattices/Enumeration/valTraceOk_more.lean](valTraceOk_more.lean)**

@import "valTraceOk_more.lean"
**[DataTypesAsLattices/Enumeration/filterOp.lean](filterOp.lean)**

@import "filterOp.lean"
**[DataTypesAsLattices/Enumeration/myhillFilterCode.lean](myhillFilterCode.lean)**

@import "myhillFilterCode.lean"
**[DataTypesAsLattices/Enumeration/primrec_myhillFilterCode.lean](primrec_myhillFilterCode.lean)**

@import "primrec_myhillFilterCode.lean"
**[DataTypesAsLattices/Enumeration/myhillCase1Code.lean](myhillCase1Code.lean)**

@import "myhillCase1Code.lean"
**[DataTypesAsLattices/Enumeration/primrec_myhillCase1Code.lean](primrec_myhillCase1Code.lean)**

@import "primrec_myhillCase1Code.lean"
**[DataTypesAsLattices/Enumeration/condCode.lean](condCode.lean)**

@import "condCode.lean"
**[DataTypesAsLattices/Enumeration/myhillCase2Code.lean](myhillCase2Code.lean)**

@import "myhillCase2Code.lean"
**[DataTypesAsLattices/Enumeration/primrec_myhillCase2Code.lean](primrec_myhillCase2Code.lean)**

@import "primrec_myhillCase2Code.lean"
**[DataTypesAsLattices/Enumeration/valC.lean](valC.lean)**

@import "valC.lean"
**[DataTypesAsLattices/Enumeration/valNat_codes.lean](valNat_codes.lean)**

@import "valNat_codes.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_3.lean](theorem_3_3.lean)**

@import "theorem_3_3.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_4.lean](theorem_3_4.lean)**

@import "theorem_3_4.lean"
**[DataTypesAsLattices/Enumeration/myhillQ_more.lean](myhillQ_more.lean)**

@import "myhillQ_more.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_5.lean](theorem_3_5.lean)**

@import "theorem_3_5.lean"
@import "Rcomb.lean"

@import "barComb.lean"

