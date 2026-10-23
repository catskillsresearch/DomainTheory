# Enumeration and degrees

## Historical note

Reduction to a few combinators is old in combinatory logic. The device special to this model is (3.1), which folds the arithmetical combinators into the one combinator $\mathbf{G}$. The Gödel numbering and the second recursion theorem are the standard constructions, written so that arithmetic and the type-free combinators share a notation, and the incompleteness theorem is the standard one in that notation. Theorem 3.5 is the argument of Myhill and Shepherdson (1955); Martin Hyland pointed out the connection. Theorem 3.6 restates enumeration degrees, as in Rogers (1967), Sasso (1975), and Gutteridge (1971). Scott notes that this area was underdeveloped beside the theory of Turing degrees. Semigroups of combinators had been discussed by Church and by Böhm, and Theorem 3.7 reads that discussion inside $\mathbf{RE} \cap \mathbf{FUN}$.

**Dependencies.** Inside Enumeration, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Enumeration.mermaid"

## Human-English

@import "1976_Enumeration_and_degrees.english" {code_block=false}

## AI: Human-English to AI-Lean

**[DataTypesAsLattices/Enumeration/Deg_isSubalgebra.lean](Deg_isSubalgebra.lean)**

@import "Deg_isSubalgebra.lean"

**[DataTypesAsLattices/Enumeration/Gcomb_bot.lean](Gcomb_bot.lean)**

@import "Gcomb_bot.lean"

**[DataTypesAsLattices/Enumeration/Gcomb_isRE.lean](Gcomb_isRE.lean)**

@import "Gcomb_isRE.lean"

**[DataTypesAsLattices/Enumeration/Gcomb_succ.lean](Gcomb_succ.lean)**

@import "Gcomb_succ.lean"

**[DataTypesAsLattices/Enumeration/GeneratedSubalgebra_generator.lean](GeneratedSubalgebra_generator.lean)**

@import "GeneratedSubalgebra_generator.lean"

**[DataTypesAsLattices/Enumeration/GeneratedSubalgebra_isSubalgebra.lean](GeneratedSubalgebra_isSubalgebra.lean)**

@import "GeneratedSubalgebra_isSubalgebra.lean"

**[DataTypesAsLattices/Enumeration/Gpack.lean](Gpack.lean)**

@import "Gpack.lean"

**[DataTypesAsLattices/Enumeration/Gcomb.lean](Gcomb.lean)**

@import "Gcomb.lean"

**[DataTypesAsLattices/Enumeration/GeneratedFromG.lean](GeneratedFromG.lean)**

@import "GeneratedFromG.lean"

**[DataTypesAsLattices/Enumeration/Icomb_SK_app.lean](Icomb_SK_app.lean)**

@import "Icomb_SK_app.lean"

**[DataTypesAsLattices/Enumeration/Deg_self.lean](Deg_self.lean)**

@import "Deg_self.lean"

**[DataTypesAsLattices/Enumeration/Lcomb.lean](Lcomb.lean)**

@import "Lcomb.lean"

**[DataTypesAsLattices/Enumeration/Lcomb_app.lean](Lcomb_app.lean)**

@import "Lcomb_app.lean"

**[DataTypesAsLattices/Enumeration/Lterm_interp.lean](Lterm_interp.lean)**

@import "Lterm_interp.lean"

**[DataTypesAsLattices/Enumeration/Lcomb_combinatory.lean](Lcomb_combinatory.lean)**

@import "Lcomb_combinatory.lean"

**[DataTypesAsLattices/Enumeration/REPredu2eexists_param.lean](REPredu2eexists_param.lean)**

@import "REPredu2eexists_param.lean"

**[DataTypesAsLattices/Enumeration/Rcomb.lean](Rcomb.lean)**

@import "Rcomb.lean"

**[DataTypesAsLattices/Enumeration/barPos.lean](barPos.lean)**

@import "barPos.lean"

**[DataTypesAsLattices/Enumeration/barPos_one.lean](barPos_one.lean)**

@import "barPos_one.lean"

**[DataTypesAsLattices/Enumeration/barPos_two.lean](barPos_two.lean)**

@import "barPos_two.lean"

**[DataTypesAsLattices/Enumeration/barPos_zero.lean](barPos_zero.lean)**

@import "barPos_zero.lean"

**[DataTypesAsLattices/Enumeration/barStepBody.lean](barStepBody.lean)**

@import "barStepBody.lean"

**[DataTypesAsLattices/Enumeration/barStep.lean](barStep.lean)**

@import "barStep.lean"

**[DataTypesAsLattices/Enumeration/barComb.lean](barComb.lean)**

@import "barComb.lean"

**[DataTypesAsLattices/Enumeration/Gbar.lean](Gbar.lean)**

@import "Gbar.lean"

**[DataTypesAsLattices/Enumeration/barStepBody_isScottContinuous_B.lean](barStepBody_isScottContinuous_B.lean)**

@import "barStepBody_isScottContinuous_B.lean"

**[DataTypesAsLattices/Enumeration/barStep_isScottContinuous.lean](barStep_isScottContinuous.lean)**

@import "barStep_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/combinatory_mem_Deg.lean](combinatory_mem_Deg.lean)**

@import "combinatory_mem_Deg.lean"

**[DataTypesAsLattices/Enumeration/combinatory_mem_subalgebra.lean](combinatory_mem_subalgebra.lean)**

@import "combinatory_mem_subalgebra.lean"

**[DataTypesAsLattices/Enumeration/condC_app2.lean](condC_app2.lean)**

@import "condC_app2.lean"

**[DataTypesAsLattices/Enumeration/condClosed_avoids8.lean](condClosed_avoids8.lean)**

@import "condClosed_avoids8.lean"

**[DataTypesAsLattices/Enumeration/condClosed_interp.lean](condClosed_interp.lean)**

@import "condClosed_interp.lean"

**[DataTypesAsLattices/Enumeration/condSet_same.lean](condSet_same.lean)**

@import "condSet_same.lean"

**[DataTypesAsLattices/Enumeration/cond_graph_eq_bot_iff.lean](cond_graph_eq_bot_iff.lean)**

@import "cond_graph_eq_bot_iff.lean"

**[DataTypesAsLattices/Enumeration/e_subset_ofNat_iff.lean](e_subset_ofNat_iff.lean)**

@import "e_subset_ofNat_iff.lean"

**[DataTypesAsLattices/Enumeration/enumBottomTerm_avoids.lean](enumBottomTerm_avoids.lean)**

@import "enumBottomTerm_avoids.lean"

**[DataTypesAsLattices/Enumeration/enumBottomTerm_interp.lean](enumBottomTerm_interp.lean)**

@import "enumBottomTerm_interp.lean"

**[DataTypesAsLattices/Enumeration/enumComp.lean](enumComp.lean)**

@import "enumComp.lean"

**[DataTypesAsLattices/Enumeration/GeneratedSemigroup.lean](GeneratedSemigroup.lean)**

@import "GeneratedSemigroup.lean"

**[DataTypesAsLattices/Enumeration/Gcomb_app.lean](Gcomb_app.lean)**

@import "Gcomb_app.lean"

**[DataTypesAsLattices/Enumeration/Gcomb_eq_condC.lean](Gcomb_eq_condC.lean)**

@import "Gcomb_eq_condC.lean"

**[DataTypesAsLattices/Enumeration/Gcomb_zero.lean](Gcomb_zero.lean)**

@import "Gcomb_zero.lean"

**[DataTypesAsLattices/Enumeration/Gpack_ne_bot.lean](Gpack_ne_bot.lean)**

@import "Gpack_ne_bot.lean"

**[DataTypesAsLattices/Enumeration/Gpack_one.lean](Gpack_one.lean)**

@import "Gpack_one.lean"

**[DataTypesAsLattices/Enumeration/Gpack_zero.lean](Gpack_zero.lean)**

@import "Gpack_zero.lean"

**[DataTypesAsLattices/Enumeration/Extensional.lean](Extensional.lean)**

@import "Extensional.lean"

**[DataTypesAsLattices/Enumeration/Kcomb_from_G.lean](Kcomb_from_G.lean)**

@import "Kcomb_from_G.lean"

**[DataTypesAsLattices/Enumeration/RE.lean](RE.lean)**

@import "RE.lean"

**[DataTypesAsLattices/Enumeration/Scomb_from_G.lean](Scomb_from_G.lean)**

@import "Scomb_from_G.lean"

**[DataTypesAsLattices/Enumeration/ValTrace.lean](ValTrace.lean)**

@import "ValTrace.lean"

**[DataTypesAsLattices/Enumeration/applyNat.lean](applyNat.lean)**

@import "applyNat.lean"

**[DataTypesAsLattices/Enumeration/argNat.lean](argNat.lean)**

@import "argNat.lean"

**[DataTypesAsLattices/Enumeration/bitList.lean](bitList.lean)**

@import "bitList.lean"

**[DataTypesAsLattices/Enumeration/bot_combinatory.lean](bot_combinatory.lean)**

@import "bot_combinatory.lean"

**[DataTypesAsLattices/Enumeration/condC_from_G.lean](condC_from_G.lean)**

@import "condC_from_G.lean"

**[DataTypesAsLattices/Enumeration/enumComp_app.lean](enumComp_app.lean)**

@import "enumComp_app.lean"

**[DataTypesAsLattices/Enumeration/enumComp_eq_compose.lean](enumComp_eq_compose.lean)**

@import "enumComp_eq_compose.lean"

**[DataTypesAsLattices/Enumeration/enumerationUnion_left_isScottContinuous.lean](enumerationUnion_left_isScottContinuous.lean)**

@import "enumerationUnion_left_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/enumerationUnion_right_isScottContinuous.lean](enumerationUnion_right_isScottContinuous.lean)**

@import "enumerationUnion_right_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/eq_3_10_apply.lean](eq_3_10_apply.lean)**

@import "eq_3_10_apply.lean"

**[DataTypesAsLattices/Enumeration/eq_3_2.lean](eq_3_2.lean)**

@import "eq_3_2.lean"

**[DataTypesAsLattices/Enumeration/eq_3_5.lean](eq_3_5.lean)**

@import "eq_3_5.lean"

**[DataTypesAsLattices/Enumeration/eq_3_6.lean](eq_3_6.lean)**

@import "eq_3_6.lean"

**[DataTypesAsLattices/Enumeration/eq_3_8_apply.lean](eq_3_8_apply.lean)**

@import "eq_3_8_apply.lean"

**[DataTypesAsLattices/Enumeration/eq_3_8_val.lean](eq_3_8_val.lean)**

@import "eq_3_8_val.lean"

**[DataTypesAsLattices/Enumeration/eq_3_9_apply.lean](eq_3_9_apply.lean)**

@import "eq_3_9_apply.lean"

**[DataTypesAsLattices/Enumeration/eq_3_9_val.lean](eq_3_9_val.lean)**

@import "eq_3_9_val.lean"

**[DataTypesAsLattices/Enumeration/eq_3_10_val.lean](eq_3_10_val.lean)**

@import "eq_3_10_val.lean"

**[DataTypesAsLattices/Enumeration/eq_3_12.lean](eq_3_12.lean)**

@import "eq_3_12.lean"

**[DataTypesAsLattices/Enumeration/exists_triangle_succ.lean](exists_triangle_succ.lean)**

@import "exists_triangle_succ.lean"

**[DataTypesAsLattices/Enumeration/filterRealizer_realizes.lean](filterRealizer_realizes.lean)**

@import "filterRealizer_realizes.lean"

**[DataTypesAsLattices/Enumeration/filterSeq_isScottContinuous.lean](filterSeq_isScottContinuous.lean)**

@import "filterSeq_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/filterC_app.lean](filterC_app.lean)**

@import "filterC_app.lean"

**[DataTypesAsLattices/Enumeration/funRetractTerm_interp.lean](funRetractTerm_interp.lean)**

@import "funRetractTerm_interp.lean"

**[DataTypesAsLattices/Enumeration/funRetract_combinatory.lean](funRetract_combinatory.lean)**

@import "funRetract_combinatory.lean"

**[DataTypesAsLattices/Enumeration/enumComp_combinatory.lean](enumComp_combinatory.lean)**

@import "enumComp_combinatory.lean"

**[DataTypesAsLattices/Enumeration/graph_mem_FUN.lean](graph_mem_FUN.lean)**

@import "graph_mem_FUN.lean"

**[DataTypesAsLattices/Enumeration/Lcomb_mem_FUN.lean](Lcomb_mem_FUN.lean)**

@import "Lcomb_mem_FUN.lean"

**[DataTypesAsLattices/Enumeration/enumComp_mem_FUN.lean](enumComp_mem_FUN.lean)**

@import "enumComp_mem_FUN.lean"

**[DataTypesAsLattices/Enumeration/haltEnum.lean](haltEnum.lean)**

@import "haltEnum.lean"

**[DataTypesAsLattices/Enumeration/beforeHalt.lean](beforeHalt.lean)**

@import "beforeHalt.lean"

**[DataTypesAsLattices/Enumeration/BasicInst85.lean](BasicInst85.lean)**

@import "BasicInst85.lean"

**[DataTypesAsLattices/Enumeration/Avoids.lean](Avoids.lean)**

@import "Avoids.lean"

**[DataTypesAsLattices/Enumeration/Deg.lean](Deg.lean)**

@import "Deg.lean"

**[DataTypesAsLattices/Enumeration/Icomb_SK.lean](Icomb_SK.lean)**

@import "Icomb_SK.lean"

**[DataTypesAsLattices/Enumeration/Subalgebra.lean](Subalgebra.lean)**

@import "Subalgebra.lean"

**[DataTypesAsLattices/Enumeration/GeneratedSubalgebra.lean](GeneratedSubalgebra.lean)**

@import "GeneratedSubalgebra.lean"

**[DataTypesAsLattices/Enumeration/Lterm.lean](Lterm.lean)**

@import "Lterm.lean"

**[DataTypesAsLattices/Enumeration/TOT.lean](TOT.lean)**

@import "TOT.lean"

**[DataTypesAsLattices/Enumeration/condClosed.lean](condClosed.lean)**

@import "condClosed.lean"

**[DataTypesAsLattices/Enumeration/enumBottomTerm.lean](enumBottomTerm.lean)**

@import "enumBottomTerm.lean"

**[DataTypesAsLattices/Enumeration/filterNum.lean](filterNum.lean)**

@import "filterNum.lean"

**[DataTypesAsLattices/Enumeration/filterTerm.lean](filterTerm.lean)**

@import "filterTerm.lean"

**[DataTypesAsLattices/Enumeration/funRetractTerm.lean](funRetractTerm.lean)**

@import "funRetractTerm.lean"

**[DataTypesAsLattices/Enumeration/haltEnum_range_re.lean](haltEnum_range_re.lean)**

@import "haltEnum_range_re.lean"

**[DataTypesAsLattices/Enumeration/haltEnum_succ_iff.lean](haltEnum_succ_iff.lean)**

@import "haltEnum_succ_iff.lean"

**[DataTypesAsLattices/Enumeration/haltEnum_range_not_computable.lean](haltEnum_range_not_computable.lean)**

@import "haltEnum_range_not_computable.lean"

**[DataTypesAsLattices/Enumeration/interStepTerm.lean](interStepTerm.lean)**

@import "interStepTerm.lean"

**[DataTypesAsLattices/Enumeration/interStepTerm_interp.lean](interStepTerm_interp.lean)**

@import "interStepTerm_interp.lean"

**[DataTypesAsLattices/Enumeration/interC_combinatory.lean](interC_combinatory.lean)**

@import "interC_combinatory.lean"

**[DataTypesAsLattices/Enumeration/interp_avoids.lean](interp_avoids.lean)**

@import "interp_avoids.lean"

**[DataTypesAsLattices/Enumeration/kClosed.lean](kClosed.lean)**

@import "kClosed.lean"

**[DataTypesAsLattices/Enumeration/kClosed_avoids8.lean](kClosed_avoids8.lean)**

@import "kClosed_avoids8.lean"

**[DataTypesAsLattices/Enumeration/kClosed_interp.lean](kClosed_interp.lean)**

@import "kClosed_interp.lean"

**[DataTypesAsLattices/Enumeration/mem_funOf_ofNat.lean](mem_funOf_ofNat.lean)**

@import "mem_funOf_ofNat.lean"

**[DataTypesAsLattices/Enumeration/funOf_ofNat_mem_re.lean](funOf_ofNat_mem_re.lean)**

@import "funOf_ofNat_mem_re.lean"

**[DataTypesAsLattices/Enumeration/myhillRealizer_isScottContinuous.lean](myhillRealizer_isScottContinuous.lean)**

@import "myhillRealizer_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/not_mem_zero_Gcomb.lean](not_mem_zero_Gcomb.lean)**

@import "not_mem_zero_Gcomb.lean"

**[DataTypesAsLattices/Enumeration/Gcomb_app_self.lean](Gcomb_app_self.lean)**

@import "Gcomb_app_self.lean"

**[DataTypesAsLattices/Enumeration/not_mem_zero_cond_graph.lean](not_mem_zero_cond_graph.lean)**

@import "not_mem_zero_cond_graph.lean"

**[DataTypesAsLattices/Enumeration/eq_3_1.lean](eq_3_1.lean)**

@import "eq_3_1.lean"

**[DataTypesAsLattices/Enumeration/num.lean](num.lean)**

@import "num.lean"

**[DataTypesAsLattices/Enumeration/opNat.lean](opNat.lean)**

@import "opNat.lean"

**[DataTypesAsLattices/Enumeration/packList.lean](packList.lean)**

@import "packList.lean"

**[DataTypesAsLattices/Enumeration/packList_components_mem_Deg.lean](packList_components_mem_Deg.lean)**

@import "packList_components_mem_Deg.lean"

**[DataTypesAsLattices/Enumeration/packList_cons_zero.lean](packList_cons_zero.lean)**

@import "packList_cons_zero.lean"

**[DataTypesAsLattices/Enumeration/predC_from_G.lean](predC_from_G.lean)**

@import "predC_from_G.lean"

**[DataTypesAsLattices/Enumeration/predClosed.lean](predClosed.lean)**

@import "predClosed.lean"

**[DataTypesAsLattices/Enumeration/predClosed_avoids8.lean](predClosed_avoids8.lean)**

@import "predClosed_avoids8.lean"

**[DataTypesAsLattices/Enumeration/predClosed_interp.lean](predClosed_interp.lean)**

@import "predClosed_interp.lean"

**[DataTypesAsLattices/Enumeration/primrec_applyNat.lean](primrec_applyNat.lean)**

@import "primrec_applyNat.lean"

**[DataTypesAsLattices/Enumeration/primrec_diagonalInterCode.lean](primrec_diagonalInterCode.lean)**

@import "primrec_diagonalInterCode.lean"

**[DataTypesAsLattices/Enumeration/primrec_haltEnum.lean](primrec_haltEnum.lean)**

@import "primrec_haltEnum.lean"

**[DataTypesAsLattices/Enumeration/primrecPred_beforeHalt.lean](primrecPred_beforeHalt.lean)**

@import "primrecPred_beforeHalt.lean"

**[DataTypesAsLattices/Enumeration/primrec_filterNum.lean](primrec_filterNum.lean)**

@import "primrec_filterNum.lean"

**[DataTypesAsLattices/Enumeration/filterRealizer.lean](filterRealizer.lean)**

@import "filterRealizer.lean"

**[DataTypesAsLattices/Enumeration/filterEnv.lean](filterEnv.lean)**

@import "filterEnv.lean"

**[DataTypesAsLattices/Enumeration/filterC.lean](filterC.lean)**

@import "filterC.lean"

**[DataTypesAsLattices/Enumeration/filterRealizer_combinatory.lean](filterRealizer_combinatory.lean)**

@import "filterRealizer_combinatory.lean"

**[DataTypesAsLattices/Enumeration/filterEnv_combinatory.lean](filterEnv_combinatory.lean)**

@import "filterEnv_combinatory.lean"

**[DataTypesAsLattices/Enumeration/filterC_combinatory.lean](filterC_combinatory.lean)**

@import "filterC_combinatory.lean"

**[DataTypesAsLattices/Enumeration/primrec_myhillCase2Code.lean](primrec_myhillCase2Code.lean)**

@import "primrec_myhillCase2Code.lean"

**[DataTypesAsLattices/Enumeration/primrec_myhillFilterCode.lean](primrec_myhillFilterCode.lean)**

@import "primrec_myhillFilterCode.lean"

**[DataTypesAsLattices/Enumeration/primrec_myhillCase1Code.lean](primrec_myhillCase1Code.lean)**

@import "primrec_myhillCase1Code.lean"

**[DataTypesAsLattices/Enumeration/primrec_num.lean](primrec_num.lean)**

@import "primrec_num.lean"

**[DataTypesAsLattices/Enumeration/primrec_recNat.lean](primrec_recNat.lean)**

@import "primrec_recNat.lean"

**[DataTypesAsLattices/Enumeration/primrec_secondRecV.lean](primrec_secondRecV.lean)**

@import "primrec_secondRecV.lean"

**[DataTypesAsLattices/Enumeration/primrec_triangle.lean](primrec_triangle.lean)**

@import "primrec_triangle.lean"

**[DataTypesAsLattices/Enumeration/primrec_unpairW.lean](primrec_unpairW.lean)**

@import "primrec_unpairW.lean"

**[DataTypesAsLattices/Enumeration/primrecu2082_finAux.lean](primrecu2082_finAux.lean)**

@import "primrecu2082_finAux.lean"

**[DataTypesAsLattices/Enumeration/primrec_fin.lean](primrec_fin.lean)**

@import "primrec_fin.lean"

**[DataTypesAsLattices/Enumeration/realizes_valNat_mem.lean](realizes_valNat_mem.lean)**

@import "realizes_valNat_mem.lean"

**[DataTypesAsLattices/Enumeration/recNat.lean](recNat.lean)**

@import "recNat.lean"

**[DataTypesAsLattices/Enumeration/sClosed.lean](sClosed.lean)**

@import "sClosed.lean"

**[DataTypesAsLattices/Enumeration/sClosed_avoids8.lean](sClosed_avoids8.lean)**

@import "sClosed_avoids8.lean"

**[DataTypesAsLattices/Enumeration/sClosed_interp.lean](sClosed_interp.lean)**

@import "sClosed_interp.lean"

**[DataTypesAsLattices/Enumeration/secondRecSubst.lean](secondRecSubst.lean)**

@import "secondRecSubst.lean"

**[DataTypesAsLattices/Enumeration/primrec_secondRecSubst.lean](primrec_secondRecSubst.lean)**

@import "primrec_secondRecSubst.lean"

**[DataTypesAsLattices/Enumeration/secondRecSubstC.lean](secondRecSubstC.lean)**

@import "secondRecSubstC.lean"

**[DataTypesAsLattices/Enumeration/secondRecOperator.lean](secondRecOperator.lean)**

@import "secondRecOperator.lean"

**[DataTypesAsLattices/Enumeration/secondRecSubstC_combinatory.lean](secondRecSubstC_combinatory.lean)**

@import "secondRecSubstC_combinatory.lean"

**[DataTypesAsLattices/Enumeration/secondRecOperator_combinatory.lean](secondRecOperator_combinatory.lean)**

@import "secondRecOperator_combinatory.lean"

**[DataTypesAsLattices/Enumeration/secondRecSubstC_realizes.lean](secondRecSubstC_realizes.lean)**

@import "secondRecSubstC_realizes.lean"

**[DataTypesAsLattices/Enumeration/secondRecOperator_app.lean](secondRecOperator_app.lean)**

@import "secondRecOperator_app.lean"

**[DataTypesAsLattices/Enumeration/secondRecVal.lean](secondRecVal.lean)**

@import "secondRecVal.lean"

**[DataTypesAsLattices/Enumeration/secondRecVal_isScottContinuous.lean](secondRecVal_isScottContinuous.lean)**

@import "secondRecVal_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/secondRecVal_app.lean](secondRecVal_app.lean)**

@import "secondRecVal_app.lean"

**[DataTypesAsLattices/Enumeration/seq2Term.lean](seq2Term.lean)**

@import "seq2Term.lean"

**[DataTypesAsLattices/Enumeration/Rterm.lean](Rterm.lean)**

@import "Rterm.lean"

**[DataTypesAsLattices/Enumeration/seq2Term_avoids8.lean](seq2Term_avoids8.lean)**

@import "seq2Term_avoids8.lean"

**[DataTypesAsLattices/Enumeration/seq2Term_interp.lean](seq2Term_interp.lean)**

@import "seq2Term_interp.lean"

**[DataTypesAsLattices/Enumeration/Rterm_interp.lean](Rterm_interp.lean)**

@import "Rterm_interp.lean"

**[DataTypesAsLattices/Enumeration/Rcomb_combinatory.lean](Rcomb_combinatory.lean)**

@import "Rcomb_combinatory.lean"

**[DataTypesAsLattices/Enumeration/seq2_eq_SK.lean](seq2_eq_SK.lean)**

@import "seq2_eq_SK.lean"

**[DataTypesAsLattices/Enumeration/seq2_combinatory.lean](seq2_combinatory.lean)**

@import "seq2_combinatory.lean"

**[DataTypesAsLattices/Enumeration/Gpack_combinatory.lean](Gpack_combinatory.lean)**

@import "Gpack_combinatory.lean"

**[DataTypesAsLattices/Enumeration/Gcomb_combinatory.lean](Gcomb_combinatory.lean)**

@import "Gcomb_combinatory.lean"

**[DataTypesAsLattices/Enumeration/seq2_left_isScottContinuous.lean](seq2_left_isScottContinuous.lean)**

@import "seq2_left_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/seq2_mem_subalgebra.lean](seq2_mem_subalgebra.lean)**

@import "seq2_mem_subalgebra.lean"

**[DataTypesAsLattices/Enumeration/packList_mem_subalgebra.lean](packList_mem_subalgebra.lean)**

@import "packList_mem_subalgebra.lean"

**[DataTypesAsLattices/Enumeration/seq2_right_isScottContinuous.lean](seq2_right_isScottContinuous.lean)**

@import "seq2_right_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/Rcomb_app.lean](Rcomb_app.lean)**

@import "Rcomb_app.lean"

**[DataTypesAsLattices/Enumeration/Rcomb_app_zero.lean](Rcomb_app_zero.lean)**

@import "Rcomb_app_zero.lean"

**[DataTypesAsLattices/Enumeration/Rcomb_mem_FUN.lean](Rcomb_mem_FUN.lean)**

@import "Rcomb_mem_FUN.lean"

**[DataTypesAsLattices/Enumeration/eq_3_16.lean](eq_3_16.lean)**

@import "eq_3_16.lean"

**[DataTypesAsLattices/Enumeration/eq_3_17_projections.lean](eq_3_17_projections.lean)**

@import "eq_3_17_projections.lean"

**[DataTypesAsLattices/Enumeration/eq_3_17_semigroup.lean](eq_3_17_semigroup.lean)**

@import "eq_3_17_semigroup.lean"

**[DataTypesAsLattices/Enumeration/seqConsTerm.lean](seqConsTerm.lean)**

@import "seqConsTerm.lean"

**[DataTypesAsLattices/Enumeration/barPosTerm.lean](barPosTerm.lean)**

@import "barPosTerm.lean"

**[DataTypesAsLattices/Enumeration/barStepTerm.lean](barStepTerm.lean)**

@import "barStepTerm.lean"

**[DataTypesAsLattices/Enumeration/seqConsTerm_interp.lean](seqConsTerm_interp.lean)**

@import "seqConsTerm_interp.lean"

**[DataTypesAsLattices/Enumeration/barPosTerm_interp.lean](barPosTerm_interp.lean)**

@import "barPosTerm_interp.lean"

**[DataTypesAsLattices/Enumeration/barStepTerm_interp.lean](barStepTerm_interp.lean)**

@import "barStepTerm_interp.lean"

**[DataTypesAsLattices/Enumeration/barComb_combinatory.lean](barComb_combinatory.lean)**

@import "barComb_combinatory.lean"

**[DataTypesAsLattices/Enumeration/Gbar_combinatory.lean](Gbar_combinatory.lean)**

@import "Gbar_combinatory.lean"

**[DataTypesAsLattices/Enumeration/seqCons_right_isScottContinuous.lean](seqCons_right_isScottContinuous.lean)**

@import "seqCons_right_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/barPos_isScottContinuous_u.lean](barPos_isScottContinuous_u.lean)**

@import "barPos_isScottContinuous_u.lean"

**[DataTypesAsLattices/Enumeration/barPos_isScottContinuous_x.lean](barPos_isScottContinuous_x.lean)**

@import "barPos_isScottContinuous_x.lean"

**[DataTypesAsLattices/Enumeration/barStepBody_isScottContinuous_u.lean](barStepBody_isScottContinuous_u.lean)**

@import "barStepBody_isScottContinuous_u.lean"

**[DataTypesAsLattices/Enumeration/barStepBody_isScottContinuous_x.lean](barStepBody_isScottContinuous_x.lean)**

@import "barStepBody_isScottContinuous_x.lean"

**[DataTypesAsLattices/Enumeration/barStep_app.lean](barStep_app.lean)**

@import "barStep_app.lean"

**[DataTypesAsLattices/Enumeration/eq_3_15.lean](eq_3_15.lean)**

@import "eq_3_15.lean"

**[DataTypesAsLattices/Enumeration/Gbar_mem_FUN.lean](Gbar_mem_FUN.lean)**

@import "Gbar_mem_FUN.lean"

**[DataTypesAsLattices/Enumeration/barComb_app2.lean](barComb_app2.lean)**

@import "barComb_app2.lean"

**[DataTypesAsLattices/Enumeration/barComb_on_R.lean](barComb_on_R.lean)**

@import "barComb_on_R.lean"

**[DataTypesAsLattices/Enumeration/barComb_on_barPos_R.lean](barComb_on_barPos_R.lean)**

@import "barComb_on_barPos_R.lean"

**[DataTypesAsLattices/Enumeration/eq_3_16_bar.lean](eq_3_16_bar.lean)**

@import "eq_3_16_bar.lean"

**[DataTypesAsLattices/Enumeration/eq_3_16_operator.lean](eq_3_16_operator.lean)**

@import "eq_3_16_operator.lean"

**[DataTypesAsLattices/Enumeration/eq_3_17.lean](eq_3_17.lean)**

@import "eq_3_17.lean"

**[DataTypesAsLattices/Enumeration/bar_generated.lean](bar_generated.lean)**

@import "bar_generated.lean"

**[DataTypesAsLattices/Enumeration/generatedSemigroup_mem_RE_FUN.lean](generatedSemigroup_mem_RE_FUN.lean)**

@import "generatedSemigroup_mem_RE_FUN.lean"

**[DataTypesAsLattices/Enumeration/singleGenerator.lean](singleGenerator.lean)**

@import "singleGenerator.lean"

**[DataTypesAsLattices/Enumeration/singleGenerator_app_zero.lean](singleGenerator_app_zero.lean)**

@import "singleGenerator_app_zero.lean"

**[DataTypesAsLattices/Enumeration/singleGenerator_mem_subalgebra.lean](singleGenerator_mem_subalgebra.lean)**

@import "singleGenerator_mem_subalgebra.lean"

**[DataTypesAsLattices/Enumeration/sucC_from_G.lean](sucC_from_G.lean)**

@import "sucC_from_G.lean"

**[DataTypesAsLattices/Enumeration/sucC_zero.lean](sucC_zero.lean)**

@import "sucC_zero.lean"

**[DataTypesAsLattices/Enumeration/sucClosed.lean](sucClosed.lean)**

@import "sucClosed.lean"

**[DataTypesAsLattices/Enumeration/gpackClosed.lean](gpackClosed.lean)**

@import "gpackClosed.lean"

**[DataTypesAsLattices/Enumeration/gClosed.lean](gClosed.lean)**

@import "gClosed.lean"

**[DataTypesAsLattices/Enumeration/sucClosed_avoids8.lean](sucClosed_avoids8.lean)**

@import "sucClosed_avoids8.lean"

**[DataTypesAsLattices/Enumeration/sucClosed_interp.lean](sucClosed_interp.lean)**

@import "sucClosed_interp.lean"

**[DataTypesAsLattices/Enumeration/gpackClosed_interp.lean](gpackClosed_interp.lean)**

@import "gpackClosed_interp.lean"

**[DataTypesAsLattices/Enumeration/gClosed_interp.lean](gClosed_interp.lean)**

@import "gClosed_interp.lean"

**[DataTypesAsLattices/Enumeration/unionBits.lean](unionBits.lean)**

@import "unionBits.lean"

**[DataTypesAsLattices/Enumeration/unionBits_eq.lean](unionBits_eq.lean)**

@import "unionBits_eq.lean"

**[DataTypesAsLattices/Enumeration/e_eq_unionBits.lean](e_eq_unionBits.lean)**

@import "e_eq_unionBits.lean"

**[DataTypesAsLattices/Enumeration/unionOperator_app.lean](unionOperator_app.lean)**

@import "unionOperator_app.lean"

**[DataTypesAsLattices/Enumeration/unionTerm.lean](unionTerm.lean)**

@import "unionTerm.lean"

**[DataTypesAsLattices/Enumeration/unionTerm_interp.lean](unionTerm_interp.lean)**

@import "unionTerm_interp.lean"

**[DataTypesAsLattices/Enumeration/unionOperator_combinatory.lean](unionOperator_combinatory.lean)**

@import "unionOperator_combinatory.lean"

**[DataTypesAsLattices/Enumeration/union_combinatory.lean](union_combinatory.lean)**

@import "union_combinatory.lean"

**[DataTypesAsLattices/Enumeration/unionBits_combinatory.lean](unionBits_combinatory.lean)**

@import "unionBits_combinatory.lean"

**[DataTypesAsLattices/Enumeration/e_combinatory.lean](e_combinatory.lean)**

@import "e_combinatory.lean"

**[DataTypesAsLattices/Enumeration/unpairComp.lean](unpairComp.lean)**

@import "unpairComp.lean"

**[DataTypesAsLattices/Enumeration/unpairComp_eq.lean](unpairComp_eq.lean)**

@import "unpairComp_eq.lean"

**[DataTypesAsLattices/Enumeration/mem_myhillQ.lean](mem_myhillQ.lean)**

@import "mem_myhillQ.lean"

**[DataTypesAsLattices/Enumeration/unpairWRec.lean](unpairWRec.lean)**

@import "unpairWRec.lean"

**[DataTypesAsLattices/Enumeration/unpairW.lean](unpairW.lean)**

@import "unpairW.lean"

**[DataTypesAsLattices/Enumeration/unpairWRec_succ.lean](unpairWRec_succ.lean)**

@import "unpairWRec_succ.lean"

**[DataTypesAsLattices/Enumeration/unpairWRec_lt.lean](unpairWRec_lt.lean)**

@import "unpairWRec_lt.lean"

**[DataTypesAsLattices/Enumeration/unpairWRec_min.lean](unpairWRec_min.lean)**

@import "unpairWRec_min.lean"

**[DataTypesAsLattices/Enumeration/unpairW_eq.lean](unpairW_eq.lean)**

@import "unpairW_eq.lean"

**[DataTypesAsLattices/Enumeration/primrec_unpairComp.lean](primrec_unpairComp.lean)**

@import "primrec_unpairComp.lean"

**[DataTypesAsLattices/Enumeration/vaalC_typed.lean](vaalC_typed.lean)**

@import "vaalC_typed.lean"

**[DataTypesAsLattices/Enumeration/vaalF.lean](vaalF.lean)**

@import "vaalF.lean"

**[DataTypesAsLattices/Enumeration/vaalC.lean](vaalC.lean)**

@import "vaalC.lean"

**[DataTypesAsLattices/Enumeration/vaalF_body_isScottContinuous.lean](vaalF_body_isScottContinuous.lean)**

@import "vaalF_body_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/vaalF_app.lean](vaalF_app.lean)**

@import "vaalF_app.lean"

**[DataTypesAsLattices/Enumeration/vaalF_isScottContinuous.lean](vaalF_isScottContinuous.lean)**

@import "vaalF_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/vaalC_fixedPoint.lean](vaalC_fixedPoint.lean)**

@import "vaalC_fixedPoint.lean"

**[DataTypesAsLattices/Enumeration/vaalC_unfold.lean](vaalC_unfold.lean)**

@import "vaalC_unfold.lean"

**[DataTypesAsLattices/Enumeration/vaalStepTerm.lean](vaalStepTerm.lean)**

@import "vaalStepTerm.lean"

**[DataTypesAsLattices/Enumeration/vaalStepTerm_interp.lean](vaalStepTerm_interp.lean)**

@import "vaalStepTerm_interp.lean"

**[DataTypesAsLattices/Enumeration/vaalC_combinatory.lean](vaalC_combinatory.lean)**

@import "vaalC_combinatory.lean"

**[DataTypesAsLattices/Enumeration/vaalC_computable.lean](vaalC_computable.lean)**

@import "vaalC_computable.lean"

**[DataTypesAsLattices/Enumeration/vaalTyped.lean](vaalTyped.lean)**

@import "vaalTyped.lean"

**[DataTypesAsLattices/Enumeration/valEntryJustified_mono.lean](valEntryJustified_mono.lean)**

@import "valEntryJustified_mono.lean"

**[DataTypesAsLattices/Enumeration/valNat.lean](valNat.lean)**

@import "valNat.lean"

**[DataTypesAsLattices/Enumeration/valNat_Ycode.lean](valNat_Ycode.lean)**

@import "valNat_Ycode.lean"

**[DataTypesAsLattices/Enumeration/valNat_botCode.lean](valNat_botCode.lean)**

@import "valNat_botCode.lean"

**[DataTypesAsLattices/Enumeration/valNat_combinatory.lean](valNat_combinatory.lean)**

@import "valNat_combinatory.lean"

**[DataTypesAsLattices/Enumeration/valNat_condCode.lean](valNat_condCode.lean)**

@import "valNat_condCode.lean"

**[DataTypesAsLattices/Enumeration/valNat_filterOp.lean](valNat_filterOp.lean)**

@import "valNat_filterOp.lean"

**[DataTypesAsLattices/Enumeration/valNat_interCode.lean](valNat_interCode.lean)**

@import "valNat_interCode.lean"

**[DataTypesAsLattices/Enumeration/valNat_diagonalInterCode.lean](valNat_diagonalInterCode.lean)**

@import "valNat_diagonalInterCode.lean"

**[DataTypesAsLattices/Enumeration/valNat_myhillFilterCode.lean](valNat_myhillFilterCode.lean)**

@import "valNat_myhillFilterCode.lean"

**[DataTypesAsLattices/Enumeration/valNat_myhillCase1Code.lean](valNat_myhillCase1Code.lean)**

@import "valNat_myhillCase1Code.lean"

**[DataTypesAsLattices/Enumeration/valNat_secondRecOperatorCode.lean](valNat_secondRecOperatorCode.lean)**

@import "valNat_secondRecOperatorCode.lean"

**[DataTypesAsLattices/Enumeration/valNat_succ.lean](valNat_succ.lean)**

@import "valNat_succ.lean"

**[DataTypesAsLattices/Enumeration/valNat_apply.lean](valNat_apply.lean)**

@import "valNat_apply.lean"

**[DataTypesAsLattices/Enumeration/valNat_unionCode.lean](valNat_unionCode.lean)**

@import "valNat_unionCode.lean"

**[DataTypesAsLattices/Enumeration/valNat_finAux.lean](valNat_finAux.lean)**

@import "valNat_finAux.lean"

**[DataTypesAsLattices/Enumeration/valNat_fin.lean](valNat_fin.lean)**

@import "valNat_fin.lean"

**[DataTypesAsLattices/Enumeration/valNat_myhillCase2Code.lean](valNat_myhillCase2Code.lean)**

@import "valNat_myhillCase2Code.lean"

**[DataTypesAsLattices/Enumeration/valNat_myhillCase2Code_bot.lean](valNat_myhillCase2Code_bot.lean)**

@import "valNat_myhillCase2Code_bot.lean"

**[DataTypesAsLattices/Enumeration/valNat_myhillCase2Code_ne_bot.lean](valNat_myhillCase2Code_ne_bot.lean)**

@import "valNat_myhillCase2Code_ne_bot.lean"

**[DataTypesAsLattices/Enumeration/valNat_zero.lean](valNat_zero.lean)**

@import "valNat_zero.lean"

**[DataTypesAsLattices/Enumeration/valRank.lean](valRank.lean)**

@import "valRank.lean"

**[DataTypesAsLattices/Enumeration/valStepValue.lean](valStepValue.lean)**

@import "valStepValue.lean"

**[DataTypesAsLattices/Enumeration/valStep.lean](valStep.lean)**

@import "valStep.lean"

**[DataTypesAsLattices/Enumeration/valC.lean](valC.lean)**

@import "valC.lean"

**[DataTypesAsLattices/Enumeration/valStep_body_isScottContinuous.lean](valStep_body_isScottContinuous.lean)**

@import "valStep_body_isScottContinuous.lean"

**[DataTypesAsLattices/Enumeration/valStep_app.lean](valStep_app.lean)**

@import "valStep_app.lean"

**[DataTypesAsLattices/Enumeration/valStep_app_succ.lean](valStep_app_succ.lean)**

@import "valStep_app_succ.lean"

**[DataTypesAsLattices/Enumeration/valStep_app_zero.lean](valStep_app_zero.lean)**

@import "valStep_app_zero.lean"

**[DataTypesAsLattices/Enumeration/valStage_eq_of_rank_le.lean](valStage_eq_of_rank_le.lean)**

@import "valStage_eq_of_rank_le.lean"

**[DataTypesAsLattices/Enumeration/valStage_subset.lean](valStage_subset.lean)**

@import "valStage_subset.lean"

**[DataTypesAsLattices/Enumeration/valC_valNat.lean](valC_valNat.lean)**

@import "valC_valNat.lean"

**[DataTypesAsLattices/Enumeration/valTraceG.lean](valTraceG.lean)**

@import "valTraceG.lean"

**[DataTypesAsLattices/Enumeration/valTraceG_re.lean](valTraceG_re.lean)**

@import "valTraceG_re.lean"

**[DataTypesAsLattices/Enumeration/valTraceHas.lean](valTraceHas.lean)**

@import "valTraceHas.lean"

**[DataTypesAsLattices/Enumeration/valEntryJustified.lean](valEntryJustified.lean)**

@import "valEntryJustified.lean"

**[DataTypesAsLattices/Enumeration/valTraceHas_append_left.lean](valTraceHas_append_left.lean)**

@import "valTraceHas_append_left.lean"

**[DataTypesAsLattices/Enumeration/valTraceHas_append_right.lean](valTraceHas_append_right.lean)**

@import "valTraceHas_append_right.lean"

**[DataTypesAsLattices/Enumeration/valTraceHas_iff.lean](valTraceHas_iff.lean)**

@import "valTraceHas_iff.lean"

**[DataTypesAsLattices/Enumeration/primrecRel_valTraceHas.lean](primrecRel_valTraceHas.lean)**

@import "primrecRel_valTraceHas.lean"

**[DataTypesAsLattices/Enumeration/primrecPred_valEntryJustified.lean](primrecPred_valEntryJustified.lean)**

@import "primrecPred_valEntryJustified.lean"

**[DataTypesAsLattices/Enumeration/primrecPred_valTraceStruct.lean](primrecPred_valTraceStruct.lean)**

@import "primrecPred_valTraceStruct.lean"

**[DataTypesAsLattices/Enumeration/valTraceOk_append.lean](valTraceOk_append.lean)**

@import "valTraceOk_append.lean"

**[DataTypesAsLattices/Enumeration/valTraceOk_cons.lean](valTraceOk_cons.lean)**

@import "valTraceOk_cons.lean"

**[DataTypesAsLattices/Enumeration/valTraceOk_empty.lean](valTraceOk_empty.lean)**

@import "valTraceOk_empty.lean"

**[DataTypesAsLattices/Enumeration/exists_concat_traces.lean](exists_concat_traces.lean)**

@import "exists_concat_traces.lean"

**[DataTypesAsLattices/Enumeration/valTraceOk_re.lean](valTraceOk_re.lean)**

@import "valTraceOk_re.lean"

**[DataTypesAsLattices/Enumeration/valTraceOk_sound.lean](valTraceOk_sound.lean)**

@import "valTraceOk_sound.lean"

**[DataTypesAsLattices/Enumeration/valTraceOk_zero.lean](valTraceOk_zero.lean)**

@import "valTraceOk_zero.lean"

**[DataTypesAsLattices/Enumeration/valTraceOk_complete.lean](valTraceOk_complete.lean)**

@import "valTraceOk_complete.lean"

**[DataTypesAsLattices/Enumeration/valNat_mem_iff.lean](valNat_mem_iff.lean)**

@import "valNat_mem_iff.lean"

**[DataTypesAsLattices/Enumeration/valNat_mem_re.lean](valNat_mem_re.lean)**

@import "valNat_mem_re.lean"

**[DataTypesAsLattices/Enumeration/myhillQ_isRE.lean](myhillQ_isRE.lean)**

@import "myhillQ_isRE.lean"

**[DataTypesAsLattices/Enumeration/valNat_mem_comp_primrec.lean](valNat_mem_comp_primrec.lean)**

@import "valNat_mem_comp_primrec.lean"

**[DataTypesAsLattices/Enumeration/valTraceStruct.lean](valTraceStruct.lean)**

@import "valTraceStruct.lean"

**[DataTypesAsLattices/Enumeration/valTraceOk.lean](valTraceOk.lean)**

@import "valTraceOk.lean"

## AI: AI-Lean to AI-English

@import "Deg_isSubalgebra.ai_lean_to_english" {code_block=false}

@import "Gcomb_bot.ai_lean_to_english" {code_block=false}

@import "Gcomb_isRE.ai_lean_to_english" {code_block=false}

@import "Gcomb_succ.ai_lean_to_english" {code_block=false}

@import "GeneratedSubalgebra_generator.ai_lean_to_english" {code_block=false}

@import "GeneratedSubalgebra_isSubalgebra.ai_lean_to_english" {code_block=false}

@import "Gpack.ai_lean_to_english" {code_block=false}

@import "Gcomb.ai_lean_to_english" {code_block=false}

@import "GeneratedFromG.ai_lean_to_english" {code_block=false}

@import "Icomb_SK_app.ai_lean_to_english" {code_block=false}

@import "Deg_self.ai_lean_to_english" {code_block=false}

@import "Lcomb.ai_lean_to_english" {code_block=false}

@import "Lcomb_app.ai_lean_to_english" {code_block=false}

@import "Lterm_interp.ai_lean_to_english" {code_block=false}

@import "Lcomb_combinatory.ai_lean_to_english" {code_block=false}

@import "REPredu2eexists_param.ai_lean_to_english" {code_block=false}

@import "Rcomb.ai_lean_to_english" {code_block=false}

@import "barPos.ai_lean_to_english" {code_block=false}

@import "barPos_one.ai_lean_to_english" {code_block=false}

@import "barPos_two.ai_lean_to_english" {code_block=false}

@import "barPos_zero.ai_lean_to_english" {code_block=false}

@import "barStepBody.ai_lean_to_english" {code_block=false}

@import "barStep.ai_lean_to_english" {code_block=false}

@import "barComb.ai_lean_to_english" {code_block=false}

@import "Gbar.ai_lean_to_english" {code_block=false}

@import "barStepBody_isScottContinuous_B.ai_lean_to_english" {code_block=false}

@import "barStep_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "combinatory_mem_Deg.ai_lean_to_english" {code_block=false}

@import "combinatory_mem_subalgebra.ai_lean_to_english" {code_block=false}

@import "condC_app2.ai_lean_to_english" {code_block=false}

@import "condClosed_avoids8.ai_lean_to_english" {code_block=false}

@import "condClosed_interp.ai_lean_to_english" {code_block=false}

@import "condSet_same.ai_lean_to_english" {code_block=false}

@import "cond_graph_eq_bot_iff.ai_lean_to_english" {code_block=false}

@import "e_subset_ofNat_iff.ai_lean_to_english" {code_block=false}

@import "enumBottomTerm_avoids.ai_lean_to_english" {code_block=false}

@import "enumBottomTerm_interp.ai_lean_to_english" {code_block=false}

@import "enumComp.ai_lean_to_english" {code_block=false}

@import "GeneratedSemigroup.ai_lean_to_english" {code_block=false}

@import "Gcomb_app.ai_lean_to_english" {code_block=false}

@import "Gcomb_eq_condC.ai_lean_to_english" {code_block=false}

@import "Gcomb_zero.ai_lean_to_english" {code_block=false}

@import "Gpack_ne_bot.ai_lean_to_english" {code_block=false}

@import "Gpack_one.ai_lean_to_english" {code_block=false}

@import "Gpack_zero.ai_lean_to_english" {code_block=false}

@import "Extensional.ai_lean_to_english" {code_block=false}

@import "Kcomb_from_G.ai_lean_to_english" {code_block=false}

@import "RE.ai_lean_to_english" {code_block=false}

@import "Scomb_from_G.ai_lean_to_english" {code_block=false}

@import "ValTrace.ai_lean_to_english" {code_block=false}

@import "applyNat.ai_lean_to_english" {code_block=false}

@import "argNat.ai_lean_to_english" {code_block=false}

@import "bitList.ai_lean_to_english" {code_block=false}

@import "bot_combinatory.ai_lean_to_english" {code_block=false}

@import "condC_from_G.ai_lean_to_english" {code_block=false}

@import "enumComp_app.ai_lean_to_english" {code_block=false}

@import "enumComp_eq_compose.ai_lean_to_english" {code_block=false}

@import "enumerationUnion_left_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "enumerationUnion_right_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "eq_3_10_apply.ai_lean_to_english" {code_block=false}

@import "eq_3_2.ai_lean_to_english" {code_block=false}

@import "eq_3_5.ai_lean_to_english" {code_block=false}

@import "eq_3_6.ai_lean_to_english" {code_block=false}

@import "eq_3_8_apply.ai_lean_to_english" {code_block=false}

@import "eq_3_8_val.ai_lean_to_english" {code_block=false}

@import "eq_3_9_apply.ai_lean_to_english" {code_block=false}

@import "eq_3_9_val.ai_lean_to_english" {code_block=false}

@import "eq_3_10_val.ai_lean_to_english" {code_block=false}

@import "eq_3_12.ai_lean_to_english" {code_block=false}

@import "exists_triangle_succ.ai_lean_to_english" {code_block=false}

@import "filterRealizer_realizes.ai_lean_to_english" {code_block=false}

@import "filterSeq_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "filterC_app.ai_lean_to_english" {code_block=false}

@import "funRetractTerm_interp.ai_lean_to_english" {code_block=false}

@import "funRetract_combinatory.ai_lean_to_english" {code_block=false}

@import "enumComp_combinatory.ai_lean_to_english" {code_block=false}

@import "graph_mem_FUN.ai_lean_to_english" {code_block=false}

@import "Lcomb_mem_FUN.ai_lean_to_english" {code_block=false}

@import "enumComp_mem_FUN.ai_lean_to_english" {code_block=false}

@import "haltEnum.ai_lean_to_english" {code_block=false}

@import "beforeHalt.ai_lean_to_english" {code_block=false}

@import "BasicInst85.ai_lean_to_english" {code_block=false}

@import "Avoids.ai_lean_to_english" {code_block=false}

@import "Deg.ai_lean_to_english" {code_block=false}

@import "Icomb_SK.ai_lean_to_english" {code_block=false}

@import "Subalgebra.ai_lean_to_english" {code_block=false}

@import "GeneratedSubalgebra.ai_lean_to_english" {code_block=false}

@import "Lterm.ai_lean_to_english" {code_block=false}

@import "TOT.ai_lean_to_english" {code_block=false}

@import "condClosed.ai_lean_to_english" {code_block=false}

@import "enumBottomTerm.ai_lean_to_english" {code_block=false}

@import "filterNum.ai_lean_to_english" {code_block=false}

@import "filterTerm.ai_lean_to_english" {code_block=false}

@import "funRetractTerm.ai_lean_to_english" {code_block=false}

@import "haltEnum_range_re.ai_lean_to_english" {code_block=false}

@import "haltEnum_succ_iff.ai_lean_to_english" {code_block=false}

@import "haltEnum_range_not_computable.ai_lean_to_english" {code_block=false}

@import "interStepTerm.ai_lean_to_english" {code_block=false}

@import "interStepTerm_interp.ai_lean_to_english" {code_block=false}

@import "interC_combinatory.ai_lean_to_english" {code_block=false}

@import "interp_avoids.ai_lean_to_english" {code_block=false}

@import "kClosed.ai_lean_to_english" {code_block=false}

@import "kClosed_avoids8.ai_lean_to_english" {code_block=false}

@import "kClosed_interp.ai_lean_to_english" {code_block=false}

@import "mem_funOf_ofNat.ai_lean_to_english" {code_block=false}

@import "funOf_ofNat_mem_re.ai_lean_to_english" {code_block=false}

@import "myhillRealizer_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "not_mem_zero_Gcomb.ai_lean_to_english" {code_block=false}

@import "Gcomb_app_self.ai_lean_to_english" {code_block=false}

@import "not_mem_zero_cond_graph.ai_lean_to_english" {code_block=false}

@import "eq_3_1.ai_lean_to_english" {code_block=false}

@import "num.ai_lean_to_english" {code_block=false}

@import "opNat.ai_lean_to_english" {code_block=false}

@import "packList.ai_lean_to_english" {code_block=false}

@import "packList_components_mem_Deg.ai_lean_to_english" {code_block=false}

@import "packList_cons_zero.ai_lean_to_english" {code_block=false}

@import "predC_from_G.ai_lean_to_english" {code_block=false}

@import "predClosed.ai_lean_to_english" {code_block=false}

@import "predClosed_avoids8.ai_lean_to_english" {code_block=false}

@import "predClosed_interp.ai_lean_to_english" {code_block=false}

@import "primrec_applyNat.ai_lean_to_english" {code_block=false}

@import "primrec_diagonalInterCode.ai_lean_to_english" {code_block=false}

@import "primrec_haltEnum.ai_lean_to_english" {code_block=false}

@import "primrecPred_beforeHalt.ai_lean_to_english" {code_block=false}

@import "primrec_filterNum.ai_lean_to_english" {code_block=false}

@import "filterRealizer.ai_lean_to_english" {code_block=false}

@import "filterEnv.ai_lean_to_english" {code_block=false}

@import "filterC.ai_lean_to_english" {code_block=false}

@import "filterRealizer_combinatory.ai_lean_to_english" {code_block=false}

@import "filterEnv_combinatory.ai_lean_to_english" {code_block=false}

@import "filterC_combinatory.ai_lean_to_english" {code_block=false}

@import "primrec_myhillCase2Code.ai_lean_to_english" {code_block=false}

@import "primrec_myhillFilterCode.ai_lean_to_english" {code_block=false}

@import "primrec_myhillCase1Code.ai_lean_to_english" {code_block=false}

@import "primrec_num.ai_lean_to_english" {code_block=false}

@import "primrec_recNat.ai_lean_to_english" {code_block=false}

@import "primrec_secondRecV.ai_lean_to_english" {code_block=false}

@import "primrec_triangle.ai_lean_to_english" {code_block=false}

@import "primrec_unpairW.ai_lean_to_english" {code_block=false}

@import "primrecu2082_finAux.ai_lean_to_english" {code_block=false}

@import "primrec_fin.ai_lean_to_english" {code_block=false}

@import "realizes_valNat_mem.ai_lean_to_english" {code_block=false}

@import "recNat.ai_lean_to_english" {code_block=false}

@import "sClosed.ai_lean_to_english" {code_block=false}

@import "sClosed_avoids8.ai_lean_to_english" {code_block=false}

@import "sClosed_interp.ai_lean_to_english" {code_block=false}

@import "secondRecSubst.ai_lean_to_english" {code_block=false}

@import "primrec_secondRecSubst.ai_lean_to_english" {code_block=false}

@import "secondRecSubstC.ai_lean_to_english" {code_block=false}

@import "secondRecOperator.ai_lean_to_english" {code_block=false}

@import "secondRecSubstC_combinatory.ai_lean_to_english" {code_block=false}

@import "secondRecOperator_combinatory.ai_lean_to_english" {code_block=false}

@import "secondRecSubstC_realizes.ai_lean_to_english" {code_block=false}

@import "secondRecOperator_app.ai_lean_to_english" {code_block=false}

@import "secondRecVal.ai_lean_to_english" {code_block=false}

@import "secondRecVal_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "secondRecVal_app.ai_lean_to_english" {code_block=false}

@import "seq2Term.ai_lean_to_english" {code_block=false}

@import "Rterm.ai_lean_to_english" {code_block=false}

@import "seq2Term_avoids8.ai_lean_to_english" {code_block=false}

@import "seq2Term_interp.ai_lean_to_english" {code_block=false}

@import "Rterm_interp.ai_lean_to_english" {code_block=false}

@import "Rcomb_combinatory.ai_lean_to_english" {code_block=false}

@import "seq2_eq_SK.ai_lean_to_english" {code_block=false}

@import "seq2_combinatory.ai_lean_to_english" {code_block=false}

@import "Gpack_combinatory.ai_lean_to_english" {code_block=false}

@import "Gcomb_combinatory.ai_lean_to_english" {code_block=false}

@import "seq2_left_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "seq2_mem_subalgebra.ai_lean_to_english" {code_block=false}

@import "packList_mem_subalgebra.ai_lean_to_english" {code_block=false}

@import "seq2_right_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "Rcomb_app.ai_lean_to_english" {code_block=false}

@import "Rcomb_app_zero.ai_lean_to_english" {code_block=false}

@import "Rcomb_mem_FUN.ai_lean_to_english" {code_block=false}

@import "eq_3_16.ai_lean_to_english" {code_block=false}

@import "eq_3_17_projections.ai_lean_to_english" {code_block=false}

@import "eq_3_17_semigroup.ai_lean_to_english" {code_block=false}

@import "seqConsTerm.ai_lean_to_english" {code_block=false}

@import "barPosTerm.ai_lean_to_english" {code_block=false}

@import "barStepTerm.ai_lean_to_english" {code_block=false}

@import "seqConsTerm_interp.ai_lean_to_english" {code_block=false}

@import "barPosTerm_interp.ai_lean_to_english" {code_block=false}

@import "barStepTerm_interp.ai_lean_to_english" {code_block=false}

@import "barComb_combinatory.ai_lean_to_english" {code_block=false}

@import "Gbar_combinatory.ai_lean_to_english" {code_block=false}

@import "seqCons_right_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "barPos_isScottContinuous_u.ai_lean_to_english" {code_block=false}

@import "barPos_isScottContinuous_x.ai_lean_to_english" {code_block=false}

@import "barStepBody_isScottContinuous_u.ai_lean_to_english" {code_block=false}

@import "barStepBody_isScottContinuous_x.ai_lean_to_english" {code_block=false}

@import "barStep_app.ai_lean_to_english" {code_block=false}

@import "eq_3_15.ai_lean_to_english" {code_block=false}

@import "Gbar_mem_FUN.ai_lean_to_english" {code_block=false}

@import "barComb_app2.ai_lean_to_english" {code_block=false}

@import "barComb_on_R.ai_lean_to_english" {code_block=false}

@import "barComb_on_barPos_R.ai_lean_to_english" {code_block=false}

@import "eq_3_16_bar.ai_lean_to_english" {code_block=false}

@import "eq_3_16_operator.ai_lean_to_english" {code_block=false}

@import "eq_3_17.ai_lean_to_english" {code_block=false}

@import "bar_generated.ai_lean_to_english" {code_block=false}

@import "generatedSemigroup_mem_RE_FUN.ai_lean_to_english" {code_block=false}

@import "singleGenerator.ai_lean_to_english" {code_block=false}

@import "singleGenerator_app_zero.ai_lean_to_english" {code_block=false}

@import "singleGenerator_mem_subalgebra.ai_lean_to_english" {code_block=false}

@import "sucC_from_G.ai_lean_to_english" {code_block=false}

@import "sucC_zero.ai_lean_to_english" {code_block=false}

@import "sucClosed.ai_lean_to_english" {code_block=false}

@import "gpackClosed.ai_lean_to_english" {code_block=false}

@import "gClosed.ai_lean_to_english" {code_block=false}

@import "sucClosed_avoids8.ai_lean_to_english" {code_block=false}

@import "sucClosed_interp.ai_lean_to_english" {code_block=false}

@import "gpackClosed_interp.ai_lean_to_english" {code_block=false}

@import "gClosed_interp.ai_lean_to_english" {code_block=false}

@import "unionBits.ai_lean_to_english" {code_block=false}

@import "unionBits_eq.ai_lean_to_english" {code_block=false}

@import "e_eq_unionBits.ai_lean_to_english" {code_block=false}

@import "unionOperator_app.ai_lean_to_english" {code_block=false}

@import "unionTerm.ai_lean_to_english" {code_block=false}

@import "unionTerm_interp.ai_lean_to_english" {code_block=false}

@import "unionOperator_combinatory.ai_lean_to_english" {code_block=false}

@import "union_combinatory.ai_lean_to_english" {code_block=false}

@import "unionBits_combinatory.ai_lean_to_english" {code_block=false}

@import "e_combinatory.ai_lean_to_english" {code_block=false}

@import "unpairComp.ai_lean_to_english" {code_block=false}

@import "unpairComp_eq.ai_lean_to_english" {code_block=false}

@import "mem_myhillQ.ai_lean_to_english" {code_block=false}

@import "unpairWRec.ai_lean_to_english" {code_block=false}

@import "unpairW.ai_lean_to_english" {code_block=false}

@import "unpairWRec_succ.ai_lean_to_english" {code_block=false}

@import "unpairWRec_lt.ai_lean_to_english" {code_block=false}

@import "unpairWRec_min.ai_lean_to_english" {code_block=false}

@import "unpairW_eq.ai_lean_to_english" {code_block=false}

@import "primrec_unpairComp.ai_lean_to_english" {code_block=false}

@import "vaalC_typed.ai_lean_to_english" {code_block=false}

@import "vaalF.ai_lean_to_english" {code_block=false}

@import "vaalC.ai_lean_to_english" {code_block=false}

@import "vaalF_body_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "vaalF_app.ai_lean_to_english" {code_block=false}

@import "vaalF_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "vaalC_fixedPoint.ai_lean_to_english" {code_block=false}

@import "vaalC_unfold.ai_lean_to_english" {code_block=false}

@import "vaalStepTerm.ai_lean_to_english" {code_block=false}

@import "vaalStepTerm_interp.ai_lean_to_english" {code_block=false}

@import "vaalC_combinatory.ai_lean_to_english" {code_block=false}

@import "vaalC_computable.ai_lean_to_english" {code_block=false}

@import "vaalTyped.ai_lean_to_english" {code_block=false}

@import "valEntryJustified_mono.ai_lean_to_english" {code_block=false}

@import "valNat.ai_lean_to_english" {code_block=false}

@import "valNat_Ycode.ai_lean_to_english" {code_block=false}

@import "valNat_botCode.ai_lean_to_english" {code_block=false}

@import "valNat_combinatory.ai_lean_to_english" {code_block=false}

@import "valNat_condCode.ai_lean_to_english" {code_block=false}

@import "valNat_filterOp.ai_lean_to_english" {code_block=false}

@import "valNat_interCode.ai_lean_to_english" {code_block=false}

@import "valNat_diagonalInterCode.ai_lean_to_english" {code_block=false}

@import "valNat_myhillFilterCode.ai_lean_to_english" {code_block=false}

@import "valNat_myhillCase1Code.ai_lean_to_english" {code_block=false}

@import "valNat_secondRecOperatorCode.ai_lean_to_english" {code_block=false}

@import "valNat_succ.ai_lean_to_english" {code_block=false}

@import "valNat_apply.ai_lean_to_english" {code_block=false}

@import "valNat_unionCode.ai_lean_to_english" {code_block=false}

@import "valNat_finAux.ai_lean_to_english" {code_block=false}

@import "valNat_fin.ai_lean_to_english" {code_block=false}

@import "valNat_myhillCase2Code.ai_lean_to_english" {code_block=false}

@import "valNat_myhillCase2Code_bot.ai_lean_to_english" {code_block=false}

@import "valNat_myhillCase2Code_ne_bot.ai_lean_to_english" {code_block=false}

@import "valNat_zero.ai_lean_to_english" {code_block=false}

@import "valRank.ai_lean_to_english" {code_block=false}

@import "valStepValue.ai_lean_to_english" {code_block=false}

@import "valStep.ai_lean_to_english" {code_block=false}

@import "valC.ai_lean_to_english" {code_block=false}

@import "valStep_body_isScottContinuous.ai_lean_to_english" {code_block=false}

@import "valStep_app.ai_lean_to_english" {code_block=false}

@import "valStep_app_succ.ai_lean_to_english" {code_block=false}

@import "valStep_app_zero.ai_lean_to_english" {code_block=false}

@import "valStage_eq_of_rank_le.ai_lean_to_english" {code_block=false}

@import "valStage_subset.ai_lean_to_english" {code_block=false}

@import "valC_valNat.ai_lean_to_english" {code_block=false}

@import "valTraceG.ai_lean_to_english" {code_block=false}

@import "valTraceG_re.ai_lean_to_english" {code_block=false}

@import "valTraceHas.ai_lean_to_english" {code_block=false}

@import "valEntryJustified.ai_lean_to_english" {code_block=false}

@import "valTraceHas_append_left.ai_lean_to_english" {code_block=false}

@import "valTraceHas_append_right.ai_lean_to_english" {code_block=false}

@import "valTraceHas_iff.ai_lean_to_english" {code_block=false}

@import "primrecRel_valTraceHas.ai_lean_to_english" {code_block=false}

@import "primrecPred_valEntryJustified.ai_lean_to_english" {code_block=false}

@import "primrecPred_valTraceStruct.ai_lean_to_english" {code_block=false}

@import "valTraceOk_append.ai_lean_to_english" {code_block=false}

@import "valTraceOk_cons.ai_lean_to_english" {code_block=false}

@import "valTraceOk_empty.ai_lean_to_english" {code_block=false}

@import "exists_concat_traces.ai_lean_to_english" {code_block=false}

@import "valTraceOk_re.ai_lean_to_english" {code_block=false}

@import "valTraceOk_sound.ai_lean_to_english" {code_block=false}

@import "valTraceOk_zero.ai_lean_to_english" {code_block=false}

@import "valTraceOk_complete.ai_lean_to_english" {code_block=false}

@import "valNat_mem_iff.ai_lean_to_english" {code_block=false}

@import "valNat_mem_re.ai_lean_to_english" {code_block=false}

@import "myhillQ_isRE.ai_lean_to_english" {code_block=false}

@import "valNat_mem_comp_primrec.ai_lean_to_english" {code_block=false}

@import "valTraceStruct.ai_lean_to_english" {code_block=false}

@import "valTraceOk.ai_lean_to_english" {code_block=false}

## AI: AI-English to Human-English Concordance

@import "1976_Enumeration_and_degrees.ai_english_concordance" {code_block=false}
