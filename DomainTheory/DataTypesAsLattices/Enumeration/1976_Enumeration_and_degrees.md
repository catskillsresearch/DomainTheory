# Enumeration and degrees

**Historical note.** Reduction to a few combinators is old in combinatory logic. The device special to this model is (3.1), which folds the arithmetical combinators into the one combinator $\mathbf{G}$. The Gödel numbering and the second recursion theorem are the standard constructions, written so that arithmetic and the type-free combinators share a notation, and the incompleteness theorem is the standard one in that notation. Theorem 3.5 is the argument of Myhill and Shepherdson (1955); Martin Hyland pointed out the connection. Theorem 3.6 restates enumeration degrees, as in Rogers (1967), Sasso (1975), and Gutteridge (1971). Scott notes that this area was underdeveloped beside the theory of Turing degrees. Semigroups of combinators had been discussed by Church and by Böhm, and Theorem 3.7 reads that discussion inside $\mathbf{RE} \cap \mathbf{FUN}$.

**Dependencies.** Inside Enumeration, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Enumeration.mermaid"

@import "1976_Enumeration_and_degrees.english" {code_block=false}

**[DataTypesAsLattices/Enumeration/Icomb_SK.lean](DomainTheory/DataTypesAsLattices/Enumeration/Icomb_SK.lean)**

@import "Icomb_SK.lean"
**[DataTypesAsLattices/Enumeration/graph_mem_FUN.lean](DomainTheory/DataTypesAsLattices/Enumeration/graph_mem_FUN.lean)**

@import "graph_mem_FUN.lean"
**[DataTypesAsLattices/Enumeration/seq2_eq_SK.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_eq_SK.lean)**

@import "seq2_eq_SK.lean"
**[DataTypesAsLattices/Enumeration/seq2_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_combinatory.lean)**

@import "seq2_combinatory.lean"
**[DataTypesAsLattices/Enumeration/Gpack.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gpack.lean)**

@import "Gpack.lean"
**[DataTypesAsLattices/Enumeration/Gcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb.lean)**

@import "Gcomb.lean"
**[DataTypesAsLattices/Enumeration/Subalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/Subalgebra.lean)**

@import "Subalgebra.lean"
**[DataTypesAsLattices/Enumeration/not_mem_zero_Gcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/not_mem_zero_Gcomb.lean)**

@import "not_mem_zero_Gcomb.lean"
**[DataTypesAsLattices/Enumeration/Gcomb_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb_more.lean)**

@import "Gcomb_more.lean"
**[DataTypesAsLattices/Enumeration/Deg.lean](DomainTheory/DataTypesAsLattices/Enumeration/Deg.lean)**

@import "Deg.lean"
**[DataTypesAsLattices/Enumeration/seq2_left_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_left_isScottContinuous.lean)**

@import "seq2_left_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/seq2_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_right_isScottContinuous.lean)**

@import "seq2_right_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/Rcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/Rcomb.lean)**

@import "Rcomb.lean"
**[DataTypesAsLattices/Enumeration/seqCons_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/seqCons_right_isScottContinuous.lean)**

@import "seqCons_right_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/barPos.lean](DomainTheory/DataTypesAsLattices/Enumeration/barPos.lean)**

@import "barPos.lean"
**[DataTypesAsLattices/Enumeration/barStepBody.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStepBody.lean)**

@import "barStepBody.lean"
**[DataTypesAsLattices/Enumeration/barStep.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStep.lean)**

@import "barStep.lean"
**[DataTypesAsLattices/Enumeration/enumBottomTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumBottomTerm.lean)**

@import "enumBottomTerm.lean"
**[DataTypesAsLattices/Enumeration/valNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat.lean)**

@import "valNat.lean"
**[DataTypesAsLattices/Enumeration/interp_avoids.lean](DomainTheory/DataTypesAsLattices/Enumeration/interp_avoids.lean)**

@import "interp_avoids.lean"
**[DataTypesAsLattices/Enumeration/seq2Term.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2Term.lean)**

@import "seq2Term.lean"
**[DataTypesAsLattices/Enumeration/seqConsTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/seqConsTerm.lean)**

@import "seqConsTerm.lean"
**[DataTypesAsLattices/Enumeration/barPosTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/barPosTerm.lean)**

@import "barPosTerm.lean"
**[DataTypesAsLattices/Enumeration/barStepTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStepTerm.lean)**

@import "barStepTerm.lean"
**[DataTypesAsLattices/Enumeration/barComb.lean](DomainTheory/DataTypesAsLattices/Enumeration/barComb.lean)**

@import "barComb.lean"
**[DataTypesAsLattices/Enumeration/eq_3_15.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_15.lean)**

@import "eq_3_15.lean"
**[DataTypesAsLattices/Enumeration/Gbar.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gbar.lean)**

@import "Gbar.lean"
**[DataTypesAsLattices/Enumeration/GeneratedFromG.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedFromG.lean)**

@import "GeneratedFromG.lean"
**[DataTypesAsLattices/Enumeration/Kcomb_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/Kcomb_from_G.lean)**

@import "Kcomb_from_G.lean"
**[DataTypesAsLattices/Enumeration/Scomb_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/Scomb_from_G.lean)**

@import "Scomb_from_G.lean"
**[DataTypesAsLattices/Enumeration/condC_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/condC_from_G.lean)**

@import "condC_from_G.lean"
**[DataTypesAsLattices/Enumeration/predC_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/predC_from_G.lean)**

@import "predC_from_G.lean"
**[DataTypesAsLattices/Enumeration/sucC_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/sucC_from_G.lean)**

@import "sucC_from_G.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_1.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_1.lean)**

@import "theorem_3_1.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_2.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_2.lean)**

@import "theorem_3_2.lean"
**[DataTypesAsLattices/Enumeration/unionCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionCode.lean)**

@import "unionCode.lean"
**[DataTypesAsLattices/Enumeration/botCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/botCode.lean)**

@import "botCode.lean"
**[DataTypesAsLattices/Enumeration/finAux.lean](DomainTheory/DataTypesAsLattices/Enumeration/finAux.lean)**

@import "finAux.lean"
**[DataTypesAsLattices/Enumeration/fin.lean](DomainTheory/DataTypesAsLattices/Enumeration/fin.lean)**

@import "fin.lean"
**[DataTypesAsLattices/Computability/theorem_2_6.lean](DomainTheory/DataTypesAsLattices/Computability/theorem_2_6.lean)**

@import "../Computability/theorem_2_6.lean"
**[DataTypesAsLattices/Enumeration/Lcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lcomb.lean)**

@import "Lcomb.lean"
**[DataTypesAsLattices/Enumeration/funRetractTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/funRetractTerm.lean)**

@import "funRetractTerm.lean"
**[DataTypesAsLattices/Enumeration/funRetract_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/funRetract_combinatory.lean)**

@import "funRetract_combinatory.lean"
**[DataTypesAsLattices/Enumeration/enumComp.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumComp.lean)**

@import "enumComp.lean"
**[DataTypesAsLattices/Enumeration/GeneratedSemigroup.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedSemigroup.lean)**

@import "GeneratedSemigroup.lean"
**[DataTypesAsLattices/Enumeration/haltEnum.lean](DomainTheory/DataTypesAsLattices/Enumeration/haltEnum.lean)**

@import "haltEnum.lean"
**[DataTypesAsLattices/Enumeration/beforeHalt.lean](DomainTheory/DataTypesAsLattices/Enumeration/beforeHalt.lean)**

@import "beforeHalt.lean"
**[DataTypesAsLattices/Enumeration/BasicInst85.lean](DomainTheory/DataTypesAsLattices/Enumeration/BasicInst85.lean)**

@import "BasicInst85.lean"
**[DataTypesAsLattices/Enumeration/Extensional.lean](DomainTheory/DataTypesAsLattices/Enumeration/Extensional.lean)**

@import "Extensional.lean"
**[DataTypesAsLattices/Enumeration/GeneratedSubalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedSubalgebra.lean)**

@import "GeneratedSubalgebra.lean"
**[DataTypesAsLattices/Enumeration/Lterm.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lterm.lean)**

@import "Lterm.lean"
**[DataTypesAsLattices/Enumeration/Lterm_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lterm_more.lean)**

@import "Lterm_more.lean"
**[DataTypesAsLattices/Enumeration/Lcomb_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lcomb_more.lean)**

@import "Lcomb_more.lean"
**[DataTypesAsLattices/Enumeration/REPredu2eexists_param.lean](DomainTheory/DataTypesAsLattices/Enumeration/REPredu2eexists_param.lean)**

@import "REPredu2eexists_param.lean"
**[DataTypesAsLattices/Enumeration/Rterm.lean](DomainTheory/DataTypesAsLattices/Enumeration/Rterm.lean)**

@import "Rterm.lean"
**[DataTypesAsLattices/Enumeration/Rcomb_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/Rcomb_more.lean)**

@import "Rcomb_more.lean"
**[DataTypesAsLattices/Enumeration/TOT.lean](DomainTheory/DataTypesAsLattices/Enumeration/TOT.lean)**

@import "TOT.lean"
**[DataTypesAsLattices/Enumeration/ValTrace.lean](DomainTheory/DataTypesAsLattices/Enumeration/ValTrace.lean)**

@import "ValTrace.lean"
**[DataTypesAsLattices/Enumeration/Ycode.lean](DomainTheory/DataTypesAsLattices/Enumeration/Ycode.lean)**

@import "Ycode.lean"
**[DataTypesAsLattices/Enumeration/argNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/argNat.lean)**

@import "argNat.lean"
**[DataTypesAsLattices/Enumeration/barComb_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/barComb_more.lean)**

@import "barComb_more.lean"
**[DataTypesAsLattices/Enumeration/eq_3_16.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_16.lean)**

@import "eq_3_16.lean"
**[DataTypesAsLattices/Enumeration/eq_3_17.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_17.lean)**

@import "eq_3_17.lean"
**[DataTypesAsLattices/Enumeration/bar_generated.lean](DomainTheory/DataTypesAsLattices/Enumeration/bar_generated.lean)**

@import "bar_generated.lean"
**[DataTypesAsLattices/Enumeration/bitList.lean](DomainTheory/DataTypesAsLattices/Enumeration/bitList.lean)**

@import "bitList.lean"
**[DataTypesAsLattices/Enumeration/combinatory_mem_Deg.lean](DomainTheory/DataTypesAsLattices/Enumeration/combinatory_mem_Deg.lean)**

@import "combinatory_mem_Deg.lean"
**[DataTypesAsLattices/Enumeration/combinatory_mem_subalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/combinatory_mem_subalgebra.lean)**

@import "combinatory_mem_subalgebra.lean"
**[DataTypesAsLattices/Enumeration/condC_app2.lean](DomainTheory/DataTypesAsLattices/Enumeration/condC_app2.lean)**

@import "condC_app2.lean"
**[DataTypesAsLattices/Enumeration/condClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/condClosed.lean)**

@import "condClosed.lean"
**[DataTypesAsLattices/Enumeration/condCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/condCode.lean)**

@import "condCode.lean"
**[DataTypesAsLattices/Enumeration/cond_graph_eq_bot_iff.lean](DomainTheory/DataTypesAsLattices/Enumeration/cond_graph_eq_bot_iff.lean)**

@import "cond_graph_eq_bot_iff.lean"
**[DataTypesAsLattices/Enumeration/interStepTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/interStepTerm.lean)**

@import "interStepTerm.lean"
**[DataTypesAsLattices/Enumeration/interC_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/interC_combinatory.lean)**

@import "interC_combinatory.lean"
**[DataTypesAsLattices/Enumeration/interCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/interCode.lean)**

@import "interCode.lean"
**[DataTypesAsLattices/Enumeration/diagonalInterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/diagonalInterCode.lean)**

@import "diagonalInterCode.lean"
**[DataTypesAsLattices/Enumeration/e_subset_ofNat_iff.lean](DomainTheory/DataTypesAsLattices/Enumeration/e_subset_ofNat_iff.lean)**

@import "e_subset_ofNat_iff.lean"
**[DataTypesAsLattices/Enumeration/enumerationUnion_left_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumerationUnion_left_isScottContinuous.lean)**

@import "enumerationUnion_left_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/enumerationUnion_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumerationUnion_right_isScottContinuous.lean)**

@import "enumerationUnion_right_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/not_mem_zero_cond_graph.lean](DomainTheory/DataTypesAsLattices/Enumeration/not_mem_zero_cond_graph.lean)**

@import "not_mem_zero_cond_graph.lean"
**[DataTypesAsLattices/Enumeration/eq_3_1.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_1.lean)**

@import "eq_3_1.lean"
**[DataTypesAsLattices/Enumeration/eq_3_10_apply.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_10_apply.lean)**

@import "eq_3_10_apply.lean"
**[DataTypesAsLattices/Enumeration/eq_3_8_apply.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_8_apply.lean)**

@import "eq_3_8_apply.lean"
**[DataTypesAsLattices/Enumeration/eq_3_8_val.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_8_val.lean)**

@import "eq_3_8_val.lean"
**[DataTypesAsLattices/Enumeration/eq_3_9_apply.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_9_apply.lean)**

@import "eq_3_9_apply.lean"
**[DataTypesAsLattices/Enumeration/eq_3_9_val.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_9_val.lean)**

@import "eq_3_9_val.lean"
**[DataTypesAsLattices/Enumeration/eq_3_10_val.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_10_val.lean)**

@import "eq_3_10_val.lean"
**[DataTypesAsLattices/Enumeration/eq_3_12.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_12.lean)**

@import "eq_3_12.lean"
**[DataTypesAsLattices/Enumeration/eq_3_2.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_2.lean)**

@import "eq_3_2.lean"
**[DataTypesAsLattices/Enumeration/opNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/opNat.lean)**

@import "opNat.lean"
**[DataTypesAsLattices/Enumeration/eq_3_5.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_5.lean)**

@import "eq_3_5.lean"
**[DataTypesAsLattices/Enumeration/eq_3_6.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_6.lean)**

@import "eq_3_6.lean"
**[DataTypesAsLattices/Enumeration/valTraceHas.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceHas.lean)**

@import "valTraceHas.lean"
**[DataTypesAsLattices/Enumeration/valTraceG.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceG.lean)**

@import "valTraceG.lean"
**[DataTypesAsLattices/Enumeration/exists_triangle_succ.lean](DomainTheory/DataTypesAsLattices/Enumeration/exists_triangle_succ.lean)**

@import "exists_triangle_succ.lean"
**[DataTypesAsLattices/Enumeration/unpairComp.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairComp.lean)**

@import "unpairComp.lean"
**[DataTypesAsLattices/Enumeration/valEntryJustified.lean](DomainTheory/DataTypesAsLattices/Enumeration/valEntryJustified.lean)**

@import "valEntryJustified.lean"
**[DataTypesAsLattices/Enumeration/valTraceStruct.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceStruct.lean)**

@import "valTraceStruct.lean"
**[DataTypesAsLattices/Enumeration/primrecRel_valTraceHas.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecRel_valTraceHas.lean)**

@import "primrecRel_valTraceHas.lean"
**[DataTypesAsLattices/Enumeration/unpairWRec.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairWRec.lean)**

@import "unpairWRec.lean"
**[DataTypesAsLattices/Enumeration/unpairW.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairW.lean)**

@import "unpairW.lean"
**[DataTypesAsLattices/Enumeration/primrec_triangle.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_triangle.lean)**

@import "primrec_triangle.lean"
**[DataTypesAsLattices/Enumeration/primrec_unpairW.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_unpairW.lean)**

@import "primrec_unpairW.lean"
**[DataTypesAsLattices/Enumeration/primrec_unpairComp.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_unpairComp.lean)**

@import "primrec_unpairComp.lean"
**[DataTypesAsLattices/Enumeration/primrecPred_valEntryJustified.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecPred_valEntryJustified.lean)**

@import "primrecPred_valEntryJustified.lean"
**[DataTypesAsLattices/Enumeration/primrecPred_valTraceStruct.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecPred_valTraceStruct.lean)**

@import "primrecPred_valTraceStruct.lean"
**[DataTypesAsLattices/Enumeration/valTraceOk.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk.lean)**

@import "valTraceOk.lean"
**[DataTypesAsLattices/Enumeration/exists_concat_traces.lean](DomainTheory/DataTypesAsLattices/Enumeration/exists_concat_traces.lean)**

@import "exists_concat_traces.lean"
**[DataTypesAsLattices/Enumeration/filterNum.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterNum.lean)**

@import "filterNum.lean"
**[DataTypesAsLattices/Enumeration/primrec_haltEnum.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_haltEnum.lean)**

@import "primrec_haltEnum.lean"
**[DataTypesAsLattices/Enumeration/primrecPred_beforeHalt.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecPred_beforeHalt.lean)**

@import "primrecPred_beforeHalt.lean"
**[DataTypesAsLattices/Enumeration/primrec_filterNum.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_filterNum.lean)**

@import "primrec_filterNum.lean"
**[DataTypesAsLattices/Enumeration/filterRealizer.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterRealizer.lean)**

@import "filterRealizer.lean"
**[DataTypesAsLattices/Enumeration/filterEnv.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterEnv.lean)**

@import "filterEnv.lean"
**[DataTypesAsLattices/Enumeration/filterSeq_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterSeq_isScottContinuous.lean)**

@import "filterSeq_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/filterTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterTerm.lean)**

@import "filterTerm.lean"
**[DataTypesAsLattices/Enumeration/filterC.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterC.lean)**

@import "filterC.lean"
**[DataTypesAsLattices/Enumeration/filterOp.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterOp.lean)**

@import "filterOp.lean"
**[DataTypesAsLattices/Enumeration/mem_funOf_ofNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/mem_funOf_ofNat.lean)**

@import "mem_funOf_ofNat.lean"
**[DataTypesAsLattices/Enumeration/funOf_ofNat_mem_re.lean](DomainTheory/DataTypesAsLattices/Enumeration/funOf_ofNat_mem_re.lean)**

@import "funOf_ofNat_mem_re.lean"
**[DataTypesAsLattices/Enumeration/kClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/kClosed.lean)**

@import "kClosed.lean"
**[DataTypesAsLattices/Enumeration/predClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/predClosed.lean)**

@import "predClosed.lean"
**[DataTypesAsLattices/Enumeration/sClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/sClosed.lean)**

@import "sClosed.lean"
**[DataTypesAsLattices/Enumeration/sucClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/sucClosed.lean)**

@import "sucClosed.lean"
**[DataTypesAsLattices/Enumeration/gpackClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/gpackClosed.lean)**

@import "gpackClosed.lean"
**[DataTypesAsLattices/Enumeration/gClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/gClosed.lean)**

@import "gClosed.lean"
**[DataTypesAsLattices/Enumeration/generatedSemigroup_mem_RE_FUN.lean](DomainTheory/DataTypesAsLattices/Enumeration/generatedSemigroup_mem_RE_FUN.lean)**

@import "generatedSemigroup_mem_RE_FUN.lean"
**[DataTypesAsLattices/Enumeration/seq2_mem_subalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_mem_subalgebra.lean)**

@import "seq2_mem_subalgebra.lean"
**[DataTypesAsLattices/Enumeration/packList.lean](DomainTheory/DataTypesAsLattices/Enumeration/packList.lean)**

@import "packList.lean"
**[DataTypesAsLattices/Enumeration/singleGenerator.lean](DomainTheory/DataTypesAsLattices/Enumeration/singleGenerator.lean)**

@import "singleGenerator.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_6.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_6.lean)**

@import "theorem_3_6.lean"
**[DataTypesAsLattices/Enumeration/generators_mem_singleGenerator_degree.lean](DomainTheory/DataTypesAsLattices/Enumeration/generators_mem_singleGenerator_degree.lean)**

@import "generators_mem_singleGenerator_degree.lean"
**[DataTypesAsLattices/Enumeration/haltEnum_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/haltEnum_more.lean)**

@import "haltEnum_more.lean"
**[DataTypesAsLattices/Enumeration/myhillQ.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillQ.lean)**

@import "myhillQ.lean"
**[DataTypesAsLattices/Enumeration/mem_myhillQ.lean](DomainTheory/DataTypesAsLattices/Enumeration/mem_myhillQ.lean)**

@import "mem_myhillQ.lean"
**[DataTypesAsLattices/Enumeration/myhillFilterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillFilterCode.lean)**

@import "myhillFilterCode.lean"
**[DataTypesAsLattices/Enumeration/myhillCase1Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillCase1Code.lean)**

@import "myhillCase1Code.lean"
**[DataTypesAsLattices/Enumeration/myhillCase2Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillCase2Code.lean)**

@import "myhillCase2Code.lean"
**[DataTypesAsLattices/Enumeration/realizes_valNat_mem.lean](DomainTheory/DataTypesAsLattices/Enumeration/realizes_valNat_mem.lean)**

@import "realizes_valNat_mem.lean"
**[DataTypesAsLattices/Enumeration/valRank.lean](DomainTheory/DataTypesAsLattices/Enumeration/valRank.lean)**

@import "valRank.lean"
**[DataTypesAsLattices/Enumeration/valStepValue.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStepValue.lean)**

@import "valStepValue.lean"
**[DataTypesAsLattices/Enumeration/valTraceOk_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk_more.lean)**

@import "valTraceOk_more.lean"
**[DataTypesAsLattices/Enumeration/primrec_applyNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_applyNat.lean)**

@import "primrec_applyNat.lean"
**[DataTypesAsLattices/Enumeration/primrec_num.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_num.lean)**

@import "primrec_num.lean"
**[DataTypesAsLattices/Enumeration/primrecu2082_finAux.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecu2082_finAux.lean)**

@import "primrecu2082_finAux.lean"
**[DataTypesAsLattices/Enumeration/primrec_fin.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_fin.lean)**

@import "primrec_fin.lean"
**[DataTypesAsLattices/Enumeration/recCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/recCode.lean)**

@import "recCode.lean"
**[DataTypesAsLattices/Enumeration/recNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/recNat.lean)**

@import "recNat.lean"
**[DataTypesAsLattices/Enumeration/secondRecSubst.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecSubst.lean)**

@import "secondRecSubst.lean"
**[DataTypesAsLattices/Enumeration/primrec_secondRecSubst.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_secondRecSubst.lean)**

@import "primrec_secondRecSubst.lean"
**[DataTypesAsLattices/Enumeration/secondRecSubstC.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecSubstC.lean)**

@import "secondRecSubstC.lean"
**[DataTypesAsLattices/Enumeration/secondRecVal.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecVal.lean)**

@import "secondRecVal.lean"
**[DataTypesAsLattices/Enumeration/secondRecOperator.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecOperator.lean)**

@import "secondRecOperator.lean"
**[DataTypesAsLattices/Enumeration/secondRecOperatorCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecOperatorCode.lean)**

@import "secondRecOperatorCode.lean"
**[DataTypesAsLattices/Enumeration/secondRecV.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecV.lean)**

@import "secondRecV.lean"
**[DataTypesAsLattices/Enumeration/unionOperator_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionOperator_app.lean)**

@import "unionOperator_app.lean"
**[DataTypesAsLattices/Enumeration/union_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/union_combinatory.lean)**

@import "union_combinatory.lean"
**[DataTypesAsLattices/Enumeration/unionBits.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionBits.lean)**

@import "unionBits.lean"
**[DataTypesAsLattices/Enumeration/vaalF.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalF.lean)**

@import "vaalF.lean"
**[DataTypesAsLattices/Enumeration/vaalStepTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalStepTerm.lean)**

@import "vaalStepTerm.lean"
**[DataTypesAsLattices/Enumeration/vaalC.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalC.lean)**

@import "vaalC.lean"
**[DataTypesAsLattices/Enumeration/valStep.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStep.lean)**

@import "valStep.lean"
**[DataTypesAsLattices/Enumeration/valStage_eq_of_rank_le.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStage_eq_of_rank_le.lean)**

@import "valStage_eq_of_rank_le.lean"
**[DataTypesAsLattices/Enumeration/valStage_subset.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStage_subset.lean)**

@import "valStage_subset.lean"
**[DataTypesAsLattices/Enumeration/valC.lean](DomainTheory/DataTypesAsLattices/Enumeration/valC.lean)**

@import "valC.lean"
**[DataTypesAsLattices/Functionality/treeF_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/treeF_isScottContinuous.lean)**

@import "../Functionality/treeF_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/treeR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/treeR_isRetract.lean)**

@import "../Functionality/treeR_isRetract.lean"
**[DataTypesAsLattices/Enumeration/vaalTyped.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalTyped.lean)**

@import "vaalTyped.lean"
**[DataTypesAsLattices/Enumeration/valNat_codes.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_codes.lean)**

@import "valNat_codes.lean"
**[DataTypesAsLattices/Enumeration/myhillQ_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillQ_more.lean)**

@import "myhillQ_more.lean"
**[DataTypesAsLattices/Enumeration/primrec_diagonalInterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_diagonalInterCode.lean)**

@import "primrec_diagonalInterCode.lean"
**[DataTypesAsLattices/Enumeration/primrec_myhillFilterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_myhillFilterCode.lean)**

@import "primrec_myhillFilterCode.lean"
**[DataTypesAsLattices/Enumeration/primrec_myhillCase1Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_myhillCase1Code.lean)**

@import "primrec_myhillCase1Code.lean"
**[DataTypesAsLattices/Enumeration/primrec_myhillCase2Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_myhillCase2Code.lean)**

@import "primrec_myhillCase2Code.lean"
**[DataTypesAsLattices/Enumeration/primrec_recNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_recNat.lean)**

@import "primrec_recNat.lean"
**[DataTypesAsLattices/Enumeration/primrec_secondRecV.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_secondRecV.lean)**

@import "primrec_secondRecV.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_3.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_3.lean)**

@import "theorem_3_3.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_4.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_4.lean)**

@import "theorem_3_4.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_5.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_5.lean)**

@import "theorem_3_5.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_6_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_6_more.lean)**

@import "theorem_3_6_more.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_7.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_7.lean)**

@import "theorem_3_7.lean"
**[DataTypesAsLattices/Functionality/eq_4_38.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_38.lean)**

@import "../Functionality/eq_4_38.lean"
@import "Rcomb.lean"

@import "barComb.lean"

