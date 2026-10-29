# Subsets and their classification

**Historical note.** The classification of these subsets by notions from descriptive set theory, and the connection with Wadge reducibility, are in the work of Adrian Tang. The normal forms for the classes, such as Table 3, are Scott's.

**Dependencies.** Inside Classification, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Classification.mermaid"

@import "1976_Subsets_and_their_classification.english" {code_block=false}

**[DataTypesAsLattices/Continuous/IsScottOpen.lean](../Continuous/IsScottOpen.lean)**

@import "../Continuous/IsScottOpen.lean"
**[DataTypesAsLattices/Classification/IsBooleanOpen.lean](IsBooleanOpen.lean)**

@import "IsBooleanOpen.lean"
**[DataTypesAsLattices/Continuous/isScottOpen_iff_isOpen.lean](../Continuous/isScottOpen_iff_isOpen.lean)**

@import "../Continuous/isScottOpen_iff_isOpen.lean"
**[DataTypesAsLattices/Continuous/isScottOpen_isUpper.lean](../Continuous/isScottOpen_isUpper.lean)**

@import "../Continuous/isScottOpen_isUpper.lean"
**[DataTypesAsLattices/Continuous/IsScottContinuous.lean](../Continuous/IsScottContinuous.lean)**

@import "../Continuous/IsScottContinuous.lean"
**[DataTypesAsLattices/Lambda/minExtend.lean](../Lambda/minExtend.lean)**

@import "../Lambda/minExtend.lean"
**[DataTypesAsLattices/Lambda/ScottContinuousFin.lean](../Lambda/ScottContinuousFin.lean)**

@import "../Lambda/ScottContinuousFin.lean"
**[DataTypesAsLattices/Lambda/succSet_more.lean](../Lambda/succSet_more.lean)**

@import "../Lambda/succSet_more.lean"
**[DataTypesAsLattices/Lambda/condSet.lean](../Lambda/condSet.lean)**

@import "../Lambda/condSet.lean"
**[DataTypesAsLattices/Lambda/predSet_more.lean](../Lambda/predSet_more.lean)**

@import "../Lambda/predSet_more.lean"
**[DataTypesAsLattices/Lambda/eq_2_7_succ.lean](../Lambda/eq_2_7_succ.lean)**

@import "../Lambda/eq_2_7_succ.lean"
**[DataTypesAsLattices/Lambda/eq_2_7_zero.lean](../Lambda/eq_2_7_zero.lean)**

@import "../Lambda/eq_2_7_zero.lean"
**[DataTypesAsLattices/Lambda/eq_2_7_bot.lean](../Lambda/eq_2_7_bot.lean)**

@import "../Lambda/eq_2_7_bot.lean"
**[DataTypesAsLattices/Lambda/eq_2_7_mix.lean](../Lambda/eq_2_7_mix.lean)**

@import "../Lambda/eq_2_7_mix.lean"
**[DataTypesAsLattices/Lambda/eq_2_7_pos.lean](../Lambda/eq_2_7_pos.lean)**

@import "../Lambda/eq_2_7_pos.lean"
**[DataTypesAsLattices/Lambda/condC.lean](../Lambda/condC.lean)**

@import "../Lambda/condC.lean"
**[DataTypesAsLattices/Lambda/graph_const_isScottContinuous.lean](../Lambda/graph_const_isScottContinuous.lean)**

@import "../Lambda/graph_const_isScottContinuous.lean"
**[DataTypesAsLattices/Lambda/const_isScottContinuous.lean](../Lambda/const_isScottContinuous.lean)**

@import "../Lambda/const_isScottContinuous.lean"
**[DataTypesAsLattices/Lambda/id_isScottContinuous.lean](../Lambda/id_isScottContinuous.lean)**

@import "../Lambda/id_isScottContinuous.lean"
**[DataTypesAsLattices/Lambda/eq_2_15.lean](../Lambda/eq_2_15.lean)**

@import "../Lambda/eq_2_15.lean"
**[DataTypesAsLattices/Lambda/topRec.lean](../Lambda/topRec.lean)**

@import "../Lambda/topRec.lean"
**[DataTypesAsLattices/Lambda/eq_2_16.lean](../Lambda/eq_2_16.lean)**

@import "../Lambda/eq_2_16.lean"
**[DataTypesAsLattices/Retracts/sUnion_Fixpoints_le_image.lean](../Retracts/sUnion_Fixpoints_le_image.lean)**

@import "../Retracts/sUnion_Fixpoints_le_image.lean"
**[DataTypesAsLattices/Retracts/gfpBelow.lean](../Retracts/gfpBelow.lean)**

@import "../Retracts/gfpBelow.lean"
**[DataTypesAsLattices/Retracts/iterateFrom.lean](../Retracts/iterateFrom.lean)**

@import "../Retracts/iterateFrom.lean"
**[DataTypesAsLattices/Computability/IsComputable.lean](../Computability/IsComputable.lean)**

@import "../Computability/IsComputable.lean"
**[DataTypesAsLattices/Continuous/exists_e_cover_finite.lean](../Continuous/exists_e_cover_finite.lean)**

@import "../Continuous/exists_e_cover_finite.lean"
**[DataTypesAsLattices/Continuous/theorem_1_1.lean](../Continuous/theorem_1_1.lean)**

@import "../Continuous/theorem_1_1.lean"
**[DataTypesAsLattices/FixedPoint/theorem_1_3.lean](../FixedPoint/theorem_1_3.lean)**

@import "../FixedPoint/theorem_1_3.lean"
**[DataTypesAsLattices/Lambda/iterateBot_param_isScottContinuous.lean](../Lambda/iterateBot_param_isScottContinuous.lean)**

@import "../Lambda/iterateBot_param_isScottContinuous.lean"
**[DataTypesAsLattices/Lambda/fix_param_isScottContinuous.lean](../Lambda/fix_param_isScottContinuous.lean)**

@import "../Lambda/fix_param_isScottContinuous.lean"
**[DataTypesAsLattices/FixedPoint/chain_lemma.lean](../FixedPoint/chain_lemma.lean)**

@import "../FixedPoint/chain_lemma.lean"
**[DataTypesAsLattices/Retracts/lfpAbove.lean](../Retracts/lfpAbove.lean)**

@import "../Retracts/lfpAbove.lean"
**[DataTypesAsLattices/FixedPoint/iterateBot_mono.lean](../FixedPoint/iterateBot_mono.lean)**

@import "../FixedPoint/iterateBot_mono.lean"
**[DataTypesAsLattices/FixedPoint/theorem_1_4.lean](../FixedPoint/theorem_1_4.lean)**

@import "../FixedPoint/theorem_1_4.lean"
**[DataTypesAsLattices/Graph/funOf.lean](../Graph/funOf.lean)**

@import "../Graph/funOf.lean"
**[DataTypesAsLattices/Lambda/nestApplyFin.lean](../Lambda/nestApplyFin.lean)**

@import "../Lambda/nestApplyFin.lean"
**[DataTypesAsLattices/Lambda/interp.lean](../Lambda/interp.lean)**

@import "../Lambda/interp.lean"
**[DataTypesAsLattices/Lambda/Fofg.lean](../Lambda/Fofg.lean)**

@import "../Lambda/Fofg.lean"
**[DataTypesAsLattices/Lambda/Scomb.lean](../Lambda/Scomb.lean)**

@import "../Lambda/Scomb.lean"
**[DataTypesAsLattices/Lambda/IsCombinatory.lean](../Lambda/IsCombinatory.lean)**

@import "../Lambda/IsCombinatory.lean"
**[DataTypesAsLattices/Lambda/dcondSet.lean](../Lambda/dcondSet.lean)**

@import "../Lambda/dcondSet.lean"
**[DataTypesAsLattices/Lambda/dcondSet_more.lean](../Lambda/dcondSet_more.lean)**

@import "../Lambda/dcondSet_more.lean"
**[DataTypesAsLattices/Lambda/ofComb.lean](../Lambda/ofComb.lean)**

@import "../Lambda/ofComb.lean"
**[DataTypesAsLattices/Lambda/theorem_2_1.lean](../Lambda/theorem_2_1.lean)**

@import "../Lambda/theorem_2_1.lean"
**[DataTypesAsLattices/Lambda/diagApp_isScottContinuous.lean](../Lambda/diagApp_isScottContinuous.lean)**

@import "../Lambda/diagApp_isScottContinuous.lean"
**[DataTypesAsLattices/Lambda/eq_2_9.lean](../Lambda/eq_2_9.lean)**

@import "../Lambda/eq_2_9.lean"
**[DataTypesAsLattices/Lambda/FUN.lean](../Lambda/FUN.lean)**

@import "../Lambda/FUN.lean"
**[DataTypesAsLattices/Lambda/eq_2_13.lean](../Lambda/eq_2_13.lean)**

@import "../Lambda/eq_2_13.lean"
**[DataTypesAsLattices/Lambda/eq_2_11.lean](../Lambda/eq_2_11.lean)**

@import "../Lambda/eq_2_11.lean"
**[DataTypesAsLattices/Computability/topRecTerm.lean](../Computability/topRecTerm.lean)**

@import "../Computability/topRecTerm.lean"
**[DataTypesAsLattices/Lambda/interStep.lean](../Lambda/interStep.lean)**

@import "../Lambda/interStep.lean"
**[DataTypesAsLattices/Lambda/seqFunLt.lean](../Lambda/seqFunLt.lean)**

@import "../Lambda/seqFunLt.lean"
**[DataTypesAsLattices/Lambda/mem_seqFunLt.lean](../Lambda/mem_seqFunLt.lean)**

@import "../Lambda/mem_seqFunLt.lean"
**[DataTypesAsLattices/Lambda/seqCons.lean](../Lambda/seqCons.lean)**

@import "../Lambda/seqCons.lean"
**[DataTypesAsLattices/Lambda/seqFun.lean](../Lambda/seqFun.lean)**

@import "../Lambda/seqFun.lean"
**[DataTypesAsLattices/Lambda/seqShift.lean](../Lambda/seqShift.lean)**

@import "../Lambda/seqShift.lean"
**[DataTypesAsLattices/Lambda/seqFun_more.lean](../Lambda/seqFun_more.lean)**

@import "../Lambda/seqFun_more.lean"
**[DataTypesAsLattices/Computability/LambdaDefinable.lean](../Computability/LambdaDefinable.lean)**

@import "../Computability/LambdaDefinable.lean"
**[DataTypesAsLattices/Computability/combinatory_isLambdaDefinable.lean](../Computability/combinatory_isLambdaDefinable.lean)**

@import "../Computability/combinatory_isLambdaDefinable.lean"
**[DataTypesAsLattices/Computability/Realizes.lean](../Computability/Realizes.lean)**

@import "../Computability/Realizes.lean"
**[DataTypesAsLattices/Retracts/typed.lean](../Retracts/typed.lean)**

@import "../Retracts/typed.lean"
**[DataTypesAsLattices/Retracts/dcondSet_bool_idem.lean](../Retracts/dcondSet_bool_idem.lean)**

@import "../Retracts/dcondSet_bool_idem.lean"
**[DataTypesAsLattices/Computability/addStepC.lean](../Computability/addStepC.lean)**

@import "../Computability/addStepC.lean"
**[DataTypesAsLattices/Graph/Basic/notation3.lean](../Graph/Basic/notation3.lean)**

@import "../Graph/Basic/notation3.lean"
**[DataTypesAsLattices/Graph/funOf_more.lean](../Graph/funOf_more.lean)**

@import "../Graph/funOf_more.lean"
**[DataTypesAsLattices/Retracts/IsStrict.lean](../Retracts/IsStrict.lean)**

@import "../Retracts/IsStrict.lean"
**[DataTypesAsLattices/Retracts/dcondSet_same_ofNat.lean](../Retracts/dcondSet_same_ofNat.lean)**

@import "../Retracts/dcondSet_same_ofNat.lean"
**[DataTypesAsLattices/Retracts/funOf_botElem.lean](../Retracts/funOf_botElem.lean)**

@import "../Retracts/funOf_botElem.lean"
**[DataTypesAsLattices/Retracts/theorem_4_1.lean](../Retracts/theorem_4_1.lean)**

@import "../Retracts/theorem_4_1.lean"
**[DataTypesAsLattices/Retracts/fixpointsCompleteLattice.lean](../Retracts/fixpointsCompleteLattice.lean)**

@import "../Retracts/fixpointsCompleteLattice.lean"
**[DataTypesAsLattices/Retracts/BasicInst36.lean](../Retracts/BasicInst36.lean)**

@import "../Retracts/BasicInst36.lean"
**[DataTypesAsLattices/Computability/Realizes2.lean](../Computability/Realizes2.lean)**

@import "../Computability/Realizes2.lean"
**[DataTypesAsLattices/Computability/mem_Scomb_iff.lean](../Computability/mem_Scomb_iff.lean)**

@import "../Computability/mem_Scomb_iff.lean"
**[DataTypesAsLattices/Computability/mem_condC_iff.lean](../Computability/mem_condC_iff.lean)**

@import "../Computability/mem_condC_iff.lean"
**[DataTypesAsLattices/Graph/mem_graph.lean](../Graph/mem_graph.lean)**

@import "../Graph/mem_graph.lean"
**[DataTypesAsLattices/Graph/theorem_1_2.lean](../Graph/theorem_1_2.lean)**

@import "../Graph/theorem_1_2.lean"
**[DataTypesAsLattices/Graph/beta.lean](../Graph/beta.lean)**

@import "../Graph/beta.lean"
**[DataTypesAsLattices/Lambda/curry2.lean](../Lambda/curry2.lean)**

@import "../Lambda/curry2.lean"
**[DataTypesAsLattices/Lambda/Scomb_more.lean](../Lambda/Scomb_more.lean)**

@import "../Lambda/Scomb_more.lean"
**[DataTypesAsLattices/Lambda/curryFin.lean](../Lambda/curryFin.lean)**

@import "../Lambda/curryFin.lean"
**[DataTypesAsLattices/Lambda/termShift.lean](../Lambda/termShift.lean)**

@import "../Lambda/termShift.lean"
**[DataTypesAsLattices/Lambda/condC_more.lean](../Lambda/condC_more.lean)**

@import "../Lambda/condC_more.lean"
**[DataTypesAsLattices/Lambda/curry3.lean](../Lambda/curry3.lean)**

@import "../Lambda/curry3.lean"
**[DataTypesAsLattices/Lambda/sucC_more.lean](../Lambda/sucC_more.lean)**

@import "../Lambda/sucC_more.lean"
**[DataTypesAsLattices/Lambda/predC_more.lean](../Lambda/predC_more.lean)**

@import "../Lambda/predC_more.lean"
**[DataTypesAsLattices/Lambda/Kcomb_more.lean](../Lambda/Kcomb_more.lean)**

@import "../Lambda/Kcomb_more.lean"
**[DataTypesAsLattices/Lambda/SKK_eq_I.lean](../Lambda/SKK_eq_I.lean)**

@import "../Lambda/SKK_eq_I.lean"
**[DataTypesAsLattices/Lambda/abs.lean](../Lambda/abs.lean)**

@import "../Lambda/abs.lean"
**[DataTypesAsLattices/Lambda/erase.lean](../Lambda/erase.lean)**

@import "../Lambda/erase.lean"
**[DataTypesAsLattices/Lambda/ofNat_more.lean](../Lambda/ofNat_more.lean)**

@import "../Lambda/ofNat_more.lean"
**[DataTypesAsLattices/Lambda/theorem_2_2.lean](../Lambda/theorem_2_2.lean)**

@import "../Lambda/theorem_2_2.lean"
**[DataTypesAsLattices/Lambda/primRecStepTerm.lean](../Lambda/primRecStepTerm.lean)**

@import "../Lambda/primRecStepTerm.lean"
**[DataTypesAsLattices/Lambda/primRecStep.lean](../Lambda/primRecStep.lean)**

@import "../Lambda/primRecStep.lean"
**[DataTypesAsLattices/Lambda/theorem_2_3.lean](../Lambda/theorem_2_3.lean)**

@import "../Lambda/theorem_2_3.lean"
**[DataTypesAsLattices/Lambda/theorem_2_4.lean](../Lambda/theorem_2_4.lean)**

@import "../Lambda/theorem_2_4.lean"
**[DataTypesAsLattices/Lambda/omegaComb.lean](../Lambda/omegaComb.lean)**

@import "../Lambda/omegaComb.lean"
**[DataTypesAsLattices/Lambda/omega_first_recursion.lean](../Lambda/omega_first_recursion.lean)**

@import "../Lambda/omega_first_recursion.lean"
**[DataTypesAsLattices/Lambda/Ycomb.lean](../Lambda/Ycomb.lean)**

@import "../Lambda/Ycomb.lean"
**[DataTypesAsLattices/Lambda/Yterm.lean](../Lambda/Yterm.lean)**

@import "../Lambda/Yterm.lean"
**[DataTypesAsLattices/Lambda/Ycomb_more.lean](../Lambda/Ycomb_more.lean)**

@import "../Lambda/Ycomb_more.lean"
**[DataTypesAsLattices/Lambda/theorem_2_5.lean](../Lambda/theorem_2_5.lean)**

@import "../Lambda/theorem_2_5.lean"
**[DataTypesAsLattices/Lambda/union_via_cond.lean](../Lambda/union_via_cond.lean)**

@import "../Lambda/union_via_cond.lean"
**[DataTypesAsLattices/Lambda/interC.lean](../Lambda/interC.lean)**

@import "../Lambda/interC.lean"
**[DataTypesAsLattices/Lambda/eq_2_17.lean](../Lambda/eq_2_17.lean)**

@import "../Lambda/eq_2_17.lean"
**[DataTypesAsLattices/Lambda/eq_2_14.lean](../Lambda/eq_2_14.lean)**

@import "../Lambda/eq_2_14.lean"
**[DataTypesAsLattices/Lambda/seqShift_more.lean](../Lambda/seqShift_more.lean)**

@import "../Lambda/seqShift_more.lean"
**[DataTypesAsLattices/Lambda/seqFunLt_more.lean](../Lambda/seqFunLt_more.lean)**

@import "../Lambda/seqFunLt_more.lean"
**[DataTypesAsLattices/Lambda/seq2.lean](../Lambda/seq2.lean)**

@import "../Lambda/seq2.lean"
**[DataTypesAsLattices/Lambda/eq_2_23_ge.lean](../Lambda/eq_2_23_ge.lean)**

@import "../Lambda/eq_2_23_ge.lean"
**[DataTypesAsLattices/Lambda/eq_2_23_one.lean](../Lambda/eq_2_23_one.lean)**

@import "../Lambda/eq_2_23_one.lean"
**[DataTypesAsLattices/Lambda/eq_2_23_zero.lean](../Lambda/eq_2_23_zero.lean)**

@import "../Lambda/eq_2_23_zero.lean"
**[DataTypesAsLattices/Lambda/eq_2_22.lean](../Lambda/eq_2_22.lean)**

@import "../Lambda/eq_2_22.lean"
**[DataTypesAsLattices/Lambda/dollarStepBody.lean](../Lambda/dollarStepBody.lean)**

@import "../Lambda/dollarStepBody.lean"
**[DataTypesAsLattices/Lambda/dollarStep.lean](../Lambda/dollarStep.lean)**

@import "../Lambda/dollarStep.lean"
**[DataTypesAsLattices/Lambda/termDollarStepBody.lean](../Lambda/termDollarStepBody.lean)**

@import "../Lambda/termDollarStepBody.lean"
**[DataTypesAsLattices/Lambda/termDollarStep.lean](../Lambda/termDollarStep.lean)**

@import "../Lambda/termDollarStep.lean"
**[DataTypesAsLattices/Lambda/dollarStepTerm.lean](../Lambda/dollarStepTerm.lean)**

@import "../Lambda/dollarStepTerm.lean"
**[DataTypesAsLattices/Lambda/dollarC.lean](../Lambda/dollarC.lean)**

@import "../Lambda/dollarC.lean"
**[DataTypesAsLattices/Lambda/eq_2_24.lean](../Lambda/eq_2_24.lean)**

@import "../Lambda/eq_2_24.lean"
**[DataTypesAsLattices/Lambda/eq_2_25.lean](../Lambda/eq_2_25.lean)**

@import "../Lambda/eq_2_25.lean"
**[DataTypesAsLattices/Lambda/primRecVal.lean](../Lambda/primRecVal.lean)**

@import "../Lambda/primRecVal.lean"
**[DataTypesAsLattices/Lambda/primRecHat.lean](../Lambda/primRecHat.lean)**

@import "../Lambda/primRecHat.lean"
**[DataTypesAsLattices/Computability/primRecVal_add.lean](../Computability/primRecVal_add.lean)**

@import "../Computability/primRecVal_add.lean"
**[DataTypesAsLattices/Lambda/eq_2_27.lean](../Lambda/eq_2_27.lean)**

@import "../Lambda/eq_2_27.lean"
**[DataTypesAsLattices/Computability/primRecComb.lean](../Computability/primRecComb.lean)**

@import "../Computability/primRecComb.lean"
**[DataTypesAsLattices/Lambda/Ymap.lean](../Lambda/Ymap.lean)**

@import "../Lambda/Ymap.lean"
**[DataTypesAsLattices/Lambda/eq_2_28.lean](../Lambda/eq_2_28.lean)**

@import "../Lambda/eq_2_28.lean"
**[DataTypesAsLattices/Retracts/sndC.lean](../Retracts/sndC.lean)**

@import "../Retracts/sndC.lean"
**[DataTypesAsLattices/Retracts/intF.lean](../Retracts/intF.lean)**

@import "../Retracts/intF.lean"
**[DataTypesAsLattices/Retracts/pairSeq.lean](../Retracts/pairSeq.lean)**

@import "../Retracts/pairSeq.lean"
**[DataTypesAsLattices/Retracts/comp.lean](../Retracts/comp.lean)**

@import "../Retracts/comp.lean"
**[DataTypesAsLattices/Retracts/arrowR.lean](../Retracts/arrowR.lean)**

@import "../Retracts/arrowR.lean"
**[DataTypesAsLattices/Retracts/eq_4_11.lean](../Retracts/eq_4_11.lean)**

@import "../Retracts/eq_4_11.lean"
**[DataTypesAsLattices/Computability/ComputableFin.lean](../Computability/ComputableFin.lean)**

@import "../Computability/ComputableFin.lean"
**[DataTypesAsLattices/Computability/SK_comp.lean](../Computability/SK_comp.lean)**

@import "../Computability/SK_comp.lean"
**[DataTypesAsLattices/Computability/primRecZeroC.lean](../Computability/primRecZeroC.lean)**

@import "../Computability/primRecZeroC.lean"
**[DataTypesAsLattices/Computability/addC.lean](../Computability/addC.lean)**

@import "../Computability/addC.lean"
**[DataTypesAsLattices/Computability/primRecVal_mul.lean](../Computability/primRecVal_mul.lean)**

@import "../Computability/primRecVal_mul.lean"
**[DataTypesAsLattices/Computability/botElem_combinatory.lean](../Computability/botElem_combinatory.lean)**

@import "../Computability/botElem_combinatory.lean"
**[DataTypesAsLattices/Computability/primRecOpEnv.lean](../Computability/primRecOpEnv.lean)**

@import "../Computability/primRecOpEnv.lean"
**[DataTypesAsLattices/Computability/primRecOpC.lean](../Computability/primRecOpC.lean)**

@import "../Computability/primRecOpC.lean"
**[DataTypesAsLattices/Computability/safePredC.lean](../Computability/safePredC.lean)**

@import "../Computability/safePredC.lean"
**[DataTypesAsLattices/Computability/subStepC.lean](../Computability/subStepC.lean)**

@import "../Computability/subStepC.lean"
**[DataTypesAsLattices/Computability/primRecVal_sub.lean](../Computability/primRecVal_sub.lean)**

@import "../Computability/primRecVal_sub.lean"
**[DataTypesAsLattices/Enumeration/unionTerm.lean](../Enumeration/unionTerm.lean)**

@import "../Enumeration/unionTerm.lean"
**[DataTypesAsLattices/Enumeration/unionOperator_combinatory.lean](../Enumeration/unionOperator_combinatory.lean)**

@import "../Enumeration/unionOperator_combinatory.lean"
**[DataTypesAsLattices/Retracts/Retract.lean](../Retracts/Retract.lean)**

@import "../Retracts/Retract.lean"
**[DataTypesAsLattices/Retracts/funRetract.lean](../Retracts/funRetract.lean)**

@import "../Retracts/funRetract.lean"
**[DataTypesAsLattices/Retracts/intR.lean](../Retracts/intR.lean)**

@import "../Retracts/intR.lean"
**[DataTypesAsLattices/Retracts/retract_interpolation.lean](../Retracts/retract_interpolation.lean)**

@import "../Retracts/retract_interpolation.lean"
**[DataTypesAsLattices/Retracts/boolR.lean](../Retracts/boolR.lean)**

@import "../Retracts/boolR.lean"
**[DataTypesAsLattices/Retracts/Icomb.lean](../Retracts/Icomb.lean)**

@import "../Retracts/Icomb.lean"
**[DataTypesAsLattices/Retracts/retractLe.lean](../Retracts/retractLe.lean)**

@import "../Retracts/retractLe.lean"
**[DataTypesAsLattices/Closures/Closure.lean](../Closures/Closure.lean)**

@import "../Closures/Closure.lean"
**[DataTypesAsLattices/Closures/Icomb_isClosure.lean](../Closures/Icomb_isClosure.lean)**

@import "../Closures/Icomb_isClosure.lean"
**[DataTypesAsLattices/Retracts/retract_app.lean](../Retracts/retract_app.lean)**

@import "../Retracts/retract_app.lean"
**[DataTypesAsLattices/Computability/REPredu2eand.lean](../Computability/REPredu2eand.lean)**

@import "../Computability/REPredu2eand.lean"
**[DataTypesAsLattices/Computability/REPredu2ecomp.lean](../Computability/REPredu2ecomp.lean)**

@import "../Computability/REPredu2ecomp.lean"
**[DataTypesAsLattices/Computability/REPredu2eexists.lean](../Computability/REPredu2eexists.lean)**

@import "../Computability/REPredu2eexists.lean"
**[DataTypesAsLattices/Computability/mulC.lean](../Computability/mulC.lean)**

@import "../Computability/mulC.lean"
**[DataTypesAsLattices/Computability/primrecPred_bool.lean](../Computability/primrecPred_bool.lean)**

@import "../Computability/primrecPred_bool.lean"
**[DataTypesAsLattices/Computability/primrec_enumFun.lean](../Computability/primrec_enumFun.lean)**

@import "../Computability/primrec_enumFun.lean"
**[DataTypesAsLattices/Computability/primrec_pack4_proj1.lean](../Computability/primrec_pack4_proj1.lean)**

@import "../Computability/primrec_pack4_proj1.lean"
**[DataTypesAsLattices/Computability/primrec_pack4_proj2.lean](../Computability/primrec_pack4_proj2.lean)**

@import "../Computability/primrec_pack4_proj2.lean"
**[DataTypesAsLattices/Computability/primrec_pack4_proj3.lean](../Computability/primrec_pack4_proj3.lean)**

@import "../Computability/primrec_pack4_proj3.lean"
**[DataTypesAsLattices/Computability/primrec_pack4_proj4.lean](../Computability/primrec_pack4_proj4.lean)**

@import "../Computability/primrec_pack4_proj4.lean"
**[DataTypesAsLattices/Computability/primrec_pair.lean](../Computability/primrec_pair.lean)**

@import "../Computability/primrec_pair.lean"
**[DataTypesAsLattices/Computability/IsREu2epair_mem.lean](../Computability/IsREu2epair_mem.lean)**

@import "../Computability/IsREu2epair_mem.lean"
**[DataTypesAsLattices/Computability/primrecPred_Scomb_eq.lean](../Computability/primrecPred_Scomb_eq.lean)**

@import "../Computability/primrecPred_Scomb_eq.lean"
**[DataTypesAsLattices/Computability/primrecPred_eq_scott_pair.lean](../Computability/primrecPred_eq_scott_pair.lean)**

@import "../Computability/primrecPred_eq_scott_pair.lean"
**[DataTypesAsLattices/Computability/IsREu2egraph_of_re.lean](../Computability/IsREu2egraph_of_re.lean)**

@import "../Computability/IsREu2egraph_of_re.lean"
**[DataTypesAsLattices/Computability/primrec_twoPow.lean](../Computability/primrec_twoPow.lean)**

@import "../Computability/primrec_twoPow.lean"
**[DataTypesAsLattices/Computability/primrec_testBit.lean](../Computability/primrec_testBit.lean)**

@import "../Computability/primrec_testBit.lean"
**[DataTypesAsLattices/Computability/IsREu2eKcomb.lean](../Computability/IsREu2eKcomb.lean)**

@import "../Computability/IsREu2eKcomb.lean"
**[DataTypesAsLattices/Computability/IsREu2econdC.lean](../Computability/IsREu2econdC.lean)**

@import "../Computability/IsREu2econdC.lean"
**[DataTypesAsLattices/Computability/subC.lean](../Computability/subC.lean)**

@import "../Computability/subC.lean"
**[DataTypesAsLattices/Computability/topElem_combinatory.lean](../Computability/topElem_combinatory.lean)**

@import "../Computability/topElem_combinatory.lean"
**[DataTypesAsLattices/Computability/enumRangeC.lean](../Computability/enumRangeC.lean)**

@import "../Computability/enumRangeC.lean"
**[DataTypesAsLattices/Enumeration/bot_combinatory.lean](../Enumeration/bot_combinatory.lean)**

@import "../Enumeration/bot_combinatory.lean"
**[DataTypesAsLattices/Retracts/RetractInverseLimit.lean](../Retracts/RetractInverseLimit.lean)**

@import "../Retracts/RetractInverseLimit.lean"
**[DataTypesAsLattices/Retracts/BasicInst55.lean](../Retracts/BasicInst55.lean)**

@import "../Retracts/BasicInst55.lean"
**[DataTypesAsLattices/Retracts/bot_retractLe.lean](../Retracts/bot_retractLe.lean)**

@import "../Retracts/bot_retractLe.lean"
**[DataTypesAsLattices/Retracts/curryC.lean](../Retracts/curryC.lean)**

@import "../Retracts/curryC.lean"
**[DataTypesAsLattices/Retracts/diagC.lean](../Retracts/diagC.lean)**

@import "../Retracts/diagC.lean"
**[DataTypesAsLattices/Retracts/directed_sUnion_fixed.lean](../Retracts/directed_sUnion_fixed.lean)**

@import "../Retracts/directed_sUnion_fixed.lean"
**[DataTypesAsLattices/Retracts/sSup_fixed_eq_sUnion.lean](../Retracts/sSup_fixed_eq_sUnion.lean)**

@import "../Retracts/sSup_fixed_eq_sUnion.lean"
**[DataTypesAsLattices/Retracts/retractBasis.lean](../Retracts/retractBasis.lean)**

@import "../Retracts/retractBasis.lean"
**[DataTypesAsLattices/Retracts/evalC.lean](../Retracts/evalC.lean)**

@import "../Retracts/evalC.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_mono.lean](../Retracts/inverseLimit_mono.lean)**

@import "../Retracts/inverseLimit_mono.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_chain.lean](../Retracts/inverseLimit_chain.lean)**

@import "../Retracts/inverseLimit_chain.lean"
**[DataTypesAsLattices/Computability/IsREu2egraph_of_primrecRel.lean](../Computability/IsREu2egraph_of_primrecRel.lean)**

@import "../Computability/IsREu2egraph_of_primrecRel.lean"
**[DataTypesAsLattices/Computability/IsREu2epredC.lean](../Computability/IsREu2epredC.lean)**

@import "../Computability/IsREu2epredC.lean"
**[DataTypesAsLattices/Computability/IsREu2esucC.lean](../Computability/IsREu2esucC.lean)**

@import "../Computability/IsREu2esucC.lean"
**[DataTypesAsLattices/Computability/IsREu2enumeral.lean](../Computability/IsREu2enumeral.lean)**

@import "../Computability/IsREu2enumeral.lean"
**[DataTypesAsLattices/Computability/IsREu2ezeroC.lean](../Computability/IsREu2ezeroC.lean)**

@import "../Computability/IsREu2ezeroC.lean"
**[DataTypesAsLattices/Computability/composeC.lean](../Computability/composeC.lean)**

@import "../Computability/composeC.lean"
**[DataTypesAsLattices/Computability/constComb.lean](../Computability/constComb.lean)**

@import "../Computability/constComb.lean"
**[DataTypesAsLattices/Computability/isZeroC.lean](../Computability/isZeroC.lean)**

@import "../Computability/isZeroC.lean"
**[DataTypesAsLattices/Computability/leC.lean](../Computability/leC.lean)**

@import "../Computability/leC.lean"
**[DataTypesAsLattices/Computability/sqrtEnv.lean](../Computability/sqrtEnv.lean)**

@import "../Computability/sqrtEnv.lean"
**[DataTypesAsLattices/Computability/sqrtStepC.lean](../Computability/sqrtStepC.lean)**

@import "../Computability/sqrtStepC.lean"
**[DataTypesAsLattices/Computability/primRecVal_sqrt.lean](../Computability/primRecVal_sqrt.lean)**

@import "../Computability/primRecVal_sqrt.lean"
**[DataTypesAsLattices/Computability/primrecPred_common_stage.lean](../Computability/primrecPred_common_stage.lean)**

@import "../Computability/primrecPred_common_stage.lean"
**[DataTypesAsLattices/Computability/IsREu2eeSubset.lean](../Computability/IsREu2eeSubset.lean)**

@import "../Computability/IsREu2eeSubset.lean"
**[DataTypesAsLattices/Computability/IsREu2efunOf.lean](../Computability/IsREu2efunOf.lean)**

@import "../Computability/IsREu2efunOf.lean"
**[DataTypesAsLattices/Computability/sqrtC.lean](../Computability/sqrtC.lean)**

@import "../Computability/sqrtC.lean"
**[DataTypesAsLattices/Computability/unpairEnv.lean](../Computability/unpairEnv.lean)**

@import "../Computability/unpairEnv.lean"
**[DataTypesAsLattices/Computability/unpairFstC.lean](../Computability/unpairFstC.lean)**

@import "../Computability/unpairFstC.lean"
**[DataTypesAsLattices/Computability/unpairSndC.lean](../Computability/unpairSndC.lean)**

@import "../Computability/unpairSndC.lean"
**[DataTypesAsLattices/Enumeration/RE.lean](../Enumeration/RE.lean)**

@import "../Enumeration/RE.lean"
**[DataTypesAsLattices/Computability/mem_funOf_e_iff.lean](../Computability/mem_funOf_e_iff.lean)**

@import "../Computability/mem_funOf_e_iff.lean"
**[DataTypesAsLattices/Enumeration/sucC_zero.lean](../Enumeration/sucC_zero.lean)**

@import "../Enumeration/sucC_zero.lean"
**[DataTypesAsLattices/Computability/arithEnv.lean](../Computability/arithEnv.lean)**

@import "../Computability/arithEnv.lean"
**[DataTypesAsLattices/Computability/pairComb.lean](../Computability/pairComb.lean)**

@import "../Computability/pairComb.lean"
**[DataTypesAsLattices/Computability/pairRealizer.lean](../Computability/pairRealizer.lean)**

@import "../Computability/pairRealizer.lean"
**[DataTypesAsLattices/Computability/precEnv.lean](../Computability/precEnv.lean)**

@import "../Computability/precEnv.lean"
**[DataTypesAsLattices/Computability/precC.lean](../Computability/precC.lean)**

@import "../Computability/precC.lean"
**[DataTypesAsLattices/Computability/primrec_realized.lean](../Computability/primrec_realized.lean)**

@import "../Computability/primrec_realized.lean"
**[DataTypesAsLattices/Computability/IsREu2ecombinatory.lean](../Computability/IsREu2ecombinatory.lean)**

@import "../Computability/IsREu2ecombinatory.lean"
**[DataTypesAsLattices/Computability/primrecRel_eSubset.lean](../Computability/primrecRel_eSubset.lean)**

@import "../Computability/primrecRel_eSubset.lean"
**[DataTypesAsLattices/Computability/primrecRel_mem_funOf_e.lean](../Computability/primrecRel_mem_funOf_e.lean)**

@import "../Computability/primrecRel_mem_funOf_e.lean"
**[DataTypesAsLattices/Computability/primrecRel_Scomb_bit.lean](../Computability/primrecRel_Scomb_bit.lean)**

@import "../Computability/primrecRel_Scomb_bit.lean"
**[DataTypesAsLattices/Computability/primrecPred_Scomb_subset.lean](../Computability/primrecPred_Scomb_subset.lean)**

@import "../Computability/primrecPred_Scomb_subset.lean"
**[DataTypesAsLattices/Computability/primrecRel_Scomb_app.lean](../Computability/primrecRel_Scomb_app.lean)**

@import "../Computability/primrecRel_Scomb_app.lean"
**[DataTypesAsLattices/Computability/rePred_Scomb_nested.lean](../Computability/rePred_Scomb_nested.lean)**

@import "../Computability/rePred_Scomb_nested.lean"
**[DataTypesAsLattices/Computability/IsREu2eScomb.lean](../Computability/IsREu2eScomb.lean)**

@import "../Computability/IsREu2eScomb.lean"
**[DataTypesAsLattices/Computability/combinatory_isRE.lean](../Computability/combinatory_isRE.lean)**

@import "../Computability/combinatory_isRE.lean"
**[DataTypesAsLattices/Computability/IsREu2eiff_combinatory.lean](../Computability/IsREu2eiff_combinatory.lean)**

@import "../Computability/IsREu2eiff_combinatory.lean"
**[DataTypesAsLattices/Classification/BooleanMemE.lean](BooleanMemE.lean)**

@import "BooleanMemE.lean"
**[DataTypesAsLattices/Classification/IsBdelta.lean](IsBdelta.lean)**

@import "IsBdelta.lean"
**[DataTypesAsLattices/Classification/IsFcapG.lean](IsFcapG.lean)**

@import "IsFcapG.lean"
**[DataTypesAsLattices/Classification/ScottB.lean](ScottB.lean)**

@import "ScottB.lean"
**[DataTypesAsLattices/Classification/ThreeValued.lean](ThreeValued.lean)**

@import "ThreeValued.lean"
**[DataTypesAsLattices/Classification/charOpen.lean](charOpen.lean)**

@import "charOpen.lean"
**[DataTypesAsLattices/Classification/charTop.lean](charTop.lean)**

@import "charTop.lean"
**[DataTypesAsLattices/Classification/closedToZero.lean](closedToZero.lean)**

@import "closedToZero.lean"
**[DataTypesAsLattices/Classification/evenPart.lean](evenPart.lean)**

@import "evenPart.lean"
**[DataTypesAsLattices/Classification/oddEvenPack.lean](oddEvenPack.lean)**

@import "oddEvenPack.lean"
**[DataTypesAsLattices/Classification/oddPart.lean](oddPart.lean)**

@import "oddPart.lean"
**[DataTypesAsLattices/Classification/pairIndexed.lean](pairIndexed.lean)**

@import "pairIndexed.lean"
**[DataTypesAsLattices/Classification/typicalBdelta.lean](typicalBdelta.lean)**

@import "typicalBdelta.lean"
**[DataTypesAsLattices/Classification/uvU.lean](uvU.lean)**

@import "uvU.lean"
**[DataTypesAsLattices/Classification/uvV.lean](uvV.lean)**

@import "uvV.lean"
**[DataTypesAsLattices/Classification/zeroPrime.lean](zeroPrime.lean)**

@import "zeroPrime.lean"
**[DataTypesAsLattices/Classification/Basic.lean](Basic.lean)**

@import "Basic.lean"
**[DataTypesAsLattices/Classification/IsScottGdelta.lean](IsScottGdelta.lean)**

@import "IsScottGdelta.lean"
**[DataTypesAsLattices/Classification/IsFcapGdelta.lean](IsFcapGdelta.lean)**

@import "IsFcapGdelta.lean"
**[DataTypesAsLattices/Classification/ScottF.lean](ScottF.lean)**

@import "ScottF.lean"
**[DataTypesAsLattices/Classification/fcapGdeltaPack.lean](fcapGdeltaPack.lean)**

@import "fcapGdeltaPack.lean"
**[DataTypesAsLattices/Classification/zero_not_mem_succSet_top.lean](zero_not_mem_succSet_top.lean)**

@import "zero_not_mem_succSet_top.lean"
**[DataTypesAsLattices/Classification/fcapGdeltaPack_eq.lean](fcapGdeltaPack_eq.lean)**

@import "fcapGdeltaPack_eq.lean"
**[DataTypesAsLattices/Classification/fcapGdeltaPack_isScottContinuous.lean](fcapGdeltaPack_isScottContinuous.lean)**

@import "fcapGdeltaPack_isScottContinuous.lean"
**[DataTypesAsLattices/Classification/oddEvenPack_eq_zero.lean](oddEvenPack_eq_zero.lean)**

@import "oddEvenPack_eq_zero.lean"
**[DataTypesAsLattices/Classification/pairIndexed_eq_top.lean](pairIndexed_eq_top.lean)**

@import "pairIndexed_eq_top.lean"
**[DataTypesAsLattices/Classification/theorem_6_1.lean](theorem_6_1.lean)**

@import "theorem_6_1.lean"
**[DataTypesAsLattices/Classification/theorem_6_2.lean](theorem_6_2.lean)**

@import "theorem_6_2.lean"
**[DataTypesAsLattices/Classification/theorem_6_3.lean](theorem_6_3.lean)**

@import "theorem_6_3.lean"
**[DataTypesAsLattices/Classification/theorem_6_4.lean](theorem_6_4.lean)**

@import "theorem_6_4.lean"
**[DataTypesAsLattices/Classification/theorem_6_5.lean](theorem_6_5.lean)**

@import "theorem_6_5.lean"
**[DataTypesAsLattices/Closures/Vapply.lean](../Closures/Vapply.lean)**

@import "../Closures/Vapply.lean"
**[DataTypesAsLattices/Closures/eq_5_1.lean](../Closures/eq_5_1.lean)**

@import "../Closures/eq_5_1.lean"
**[DataTypesAsLattices/Closures/eq_5_16.lean](../Closures/eq_5_16.lean)**

@import "../Closures/eq_5_16.lean"
**[DataTypesAsLattices/Closures/eq_5_17.lean](../Closures/eq_5_17.lean)**

@import "../Closures/eq_5_17.lean"
**[DataTypesAsLattices/Closures/eq_5_18.lean](../Closures/eq_5_18.lean)**

@import "../Closures/eq_5_18.lean"
**[DataTypesAsLattices/Closures/union_left_isScottContinuous.lean](../Closures/union_left_isScottContinuous.lean)**

@import "../Closures/union_left_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/union_right_isScottContinuous.lean](../Closures/union_right_isScottContinuous.lean)**

@import "../Closures/union_right_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/Vstep.lean](../Closures/Vstep.lean)**

@import "../Closures/Vstep.lean"
**[DataTypesAsLattices/Closures/VapplyY.lean](../Closures/VapplyY.lean)**

@import "../Closures/VapplyY.lean"
**[DataTypesAsLattices/Closures/Vapply_more.lean](../Closures/Vapply_more.lean)**

@import "../Closures/Vapply_more.lean"
**[DataTypesAsLattices/Closures/Vcomb.lean](../Closures/Vcomb.lean)**

@import "../Closures/Vcomb.lean"
**[DataTypesAsLattices/Closures/boxTag.lean](../Closures/boxTag.lean)**

@import "../Closures/boxTag.lean"
**[DataTypesAsLattices/Closures/closure_expansive.lean](../Closures/closure_expansive.lean)**

@import "../Closures/closure_expansive.lean"
**[DataTypesAsLattices/Closures/closureCompact.lean](../Closures/closureCompact.lean)**

@import "../Closures/closureCompact.lean"
**[DataTypesAsLattices/Closures/compactFixedBelow.lean](../Closures/compactFixedBelow.lean)**

@import "../Closures/compactFixedBelow.lean"
**[DataTypesAsLattices/Closures/representClosure.lean](../Closures/representClosure.lean)**

@import "../Closures/representClosure.lean"
**[DataTypesAsLattices/Closures/representClosureCode.lean](../Closures/representClosureCode.lean)**

@import "../Closures/representClosureCode.lean"
**[DataTypesAsLattices/Closures/representationEncode_more.lean](../Closures/representationEncode_more.lean)**

@import "../Closures/representationEncode_more.lean"
**[DataTypesAsLattices/Closures/representationOrderIso.lean](../Closures/representationOrderIso.lean)**

@import "../Closures/representationOrderIso.lean"
**[DataTypesAsLattices/Closures/retractBasis_eq_compactFixedBelow.lean](../Closures/retractBasis_eq_compactFixedBelow.lean)**

@import "../Closures/retractBasis_eq_compactFixedBelow.lean"
**[DataTypesAsLattices/Closures/fixed_eq_sSup_compacts.lean](../Closures/fixed_eq_sSup_compacts.lean)**

@import "../Closures/fixed_eq_sSup_compacts.lean"
**[DataTypesAsLattices/Closures/squareFst.lean](../Closures/squareFst.lean)**

@import "../Closures/squareFst.lean"
**[DataTypesAsLattices/Closures/eq_5_9.lean](../Closures/eq_5_9.lean)**

@import "../Closures/eq_5_9.lean"
**[DataTypesAsLattices/Closures/squareSnd.lean](../Closures/squareSnd.lean)**

@import "../Closures/squareSnd.lean"
**[DataTypesAsLattices/Closures/eq_5_10.lean](../Closures/eq_5_10.lean)**

@import "../Closures/eq_5_10.lean"
**[DataTypesAsLattices/Closures/squarePair_more.lean](../Closures/squarePair_more.lean)**

@import "../Closures/squarePair_more.lean"
**[DataTypesAsLattices/Closures/boxTensor.lean](../Closures/boxTensor.lean)**

@import "../Closures/boxTensor.lean"
**[DataTypesAsLattices/Closures/arrowR_diag_isScottContinuous.lean](../Closures/arrowR_diag_isScottContinuous.lean)**

@import "../Closures/arrowR_diag_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/selfArrowStep.lean](../Closures/selfArrowStep.lean)**

@import "../Closures/selfArrowStep.lean"
**[DataTypesAsLattices/Closures/dEq.lean](../Closures/dEq.lean)**

@import "../Closures/dEq.lean"
**[DataTypesAsLattices/Closures/compactFixedBelow_more.lean](../Closures/compactFixedBelow_more.lean)**

@import "../Closures/compactFixedBelow_more.lean"
**[DataTypesAsLattices/Closures/compact_fixed_iff.lean](../Closures/compact_fixed_iff.lean)**

@import "../Closures/compact_fixed_iff.lean"
**[DataTypesAsLattices/Closures/closureRangeCountablyAlgebraic.lean](../Closures/closureRangeCountablyAlgebraic.lean)**

@import "../Closures/closureRangeCountablyAlgebraic.lean"
**[DataTypesAsLattices/Closures/theorem_5_5.lean](../Closures/theorem_5_5.lean)**

@import "../Closures/theorem_5_5.lean"
**[DataTypesAsLattices/Closures/eq_5_11.lean](../Closures/eq_5_11.lean)**

@import "../Closures/eq_5_11.lean"
**[DataTypesAsLattices/Closures/Icomb_subset_arrowR.lean](../Closures/Icomb_subset_arrowR.lean)**

@import "../Closures/Icomb_subset_arrowR.lean"
**[DataTypesAsLattices/Closures/Icomb_subset_graph.lean](../Closures/Icomb_subset_graph.lean)**

@import "../Closures/Icomb_subset_graph.lean"
**[DataTypesAsLattices/Closures/eq_5_8.lean](../Closures/eq_5_8.lean)**

@import "../Closures/eq_5_8.lean"
**[DataTypesAsLattices/Closures/union_const_left_isScottContinuous.lean](../Closures/union_const_left_isScottContinuous.lean)**

@import "../Closures/union_const_left_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/boxShift.lean](../Closures/boxShift.lean)**

@import "../Closures/boxShift.lean"
**[DataTypesAsLattices/Closures/boxPlus.lean](../Closures/boxPlus.lean)**

@import "../Closures/boxPlus.lean"
**[DataTypesAsLattices/Closures/Icomb_subset_boxPlus.lean](../Closures/Icomb_subset_boxPlus.lean)**

@import "../Closures/Icomb_subset_boxPlus.lean"
**[DataTypesAsLattices/Closures/Icomb_subset_boxTensor.lean](../Closures/Icomb_subset_boxTensor.lean)**

@import "../Closures/Icomb_subset_boxTensor.lean"
**[DataTypesAsLattices/Closures/eq_5_12.lean](../Closures/eq_5_12.lean)**

@import "../Closures/eq_5_12.lean"
**[DataTypesAsLattices/Closures/eq_5_13.lean](../Closures/eq_5_13.lean)**

@import "../Closures/eq_5_13.lean"
**[DataTypesAsLattices/Closures/eq_5_14.lean](../Closures/eq_5_14.lean)**

@import "../Closures/eq_5_14.lean"
**[DataTypesAsLattices/Closures/eq_5_2.lean](../Closures/eq_5_2.lean)**

@import "../Closures/eq_5_2.lean"
**[DataTypesAsLattices/Closures/theorem_5_4.lean](../Closures/theorem_5_4.lean)**

@import "../Closures/theorem_5_4.lean"
**[DataTypesAsLattices/Closures/eq_5_25.lean](../Closures/eq_5_25.lean)**

@import "../Closures/eq_5_25.lean"
**[DataTypesAsLattices/Closures/openR_map_isScottContinuous.lean](../Closures/openR_map_isScottContinuous.lean)**

@import "../Closures/openR_map_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/openR_app.lean](../Closures/openR_app.lean)**

@import "../Closures/openR_app.lean"
**[DataTypesAsLattices/Closures/openR_expansive.lean](../Closures/openR_expansive.lean)**

@import "../Closures/openR_expansive.lean"
**[DataTypesAsLattices/Closures/theorem_5_1.lean](../Closures/theorem_5_1.lean)**

@import "../Closures/theorem_5_1.lean"
**[DataTypesAsLattices/Closures/theorem_5_2.lean](../Closures/theorem_5_2.lean)**

@import "../Closures/theorem_5_2.lean"
**[DataTypesAsLattices/Retracts/theorem_4_1_more.lean](../Retracts/theorem_4_1_more.lean)**

@import "../Retracts/theorem_4_1_more.lean"
**[DataTypesAsLattices/Retracts/theorem_4_2.lean](../Retracts/theorem_4_2.lean)**

@import "../Retracts/theorem_4_2.lean"
