# Subsets and their classification

**Historical note.** The classification of these subsets by notions from descriptive set theory, and the connection with Wadge reducibility, are in the work of Adrian Tang. The normal forms for the classes, such as Table 3, are Scott's.

**Dependencies.** Inside Classification, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Classification.mermaid"

@import "1976_Subsets_and_their_classification.english" {code_block=false}

**[DataTypesAsLattices/Continuous/IsScottOpen.lean](DomainTheory/DataTypesAsLattices/Continuous/IsScottOpen.lean)**

@import "../Continuous/IsScottOpen.lean"
**[DataTypesAsLattices/Classification/IsBooleanOpen.lean](DomainTheory/DataTypesAsLattices/Classification/IsBooleanOpen.lean)**

@import "IsBooleanOpen.lean"
**[DataTypesAsLattices/Continuous/isScottOpen_iff_isOpen.lean](DomainTheory/DataTypesAsLattices/Continuous/isScottOpen_iff_isOpen.lean)**

@import "../Continuous/isScottOpen_iff_isOpen.lean"
**[DataTypesAsLattices/Continuous/isScottOpen_isUpper.lean](DomainTheory/DataTypesAsLattices/Continuous/isScottOpen_isUpper.lean)**

@import "../Continuous/isScottOpen_isUpper.lean"
**[DataTypesAsLattices/Continuous/IsScottContinuous.lean](DomainTheory/DataTypesAsLattices/Continuous/IsScottContinuous.lean)**

@import "../Continuous/IsScottContinuous.lean"
**[DataTypesAsLattices/Lambda/minExtend.lean](DomainTheory/DataTypesAsLattices/Lambda/minExtend.lean)**

@import "../Lambda/minExtend.lean"
**[DataTypesAsLattices/Lambda/ScottContinuousFin.lean](DomainTheory/DataTypesAsLattices/Lambda/ScottContinuousFin.lean)**

@import "../Lambda/ScottContinuousFin.lean"
**[DataTypesAsLattices/Lambda/succSet_more.lean](DomainTheory/DataTypesAsLattices/Lambda/succSet_more.lean)**

@import "../Lambda/succSet_more.lean"
**[DataTypesAsLattices/Lambda/condSet.lean](DomainTheory/DataTypesAsLattices/Lambda/condSet.lean)**

@import "../Lambda/condSet.lean"
**[DataTypesAsLattices/Lambda/predSet_more.lean](DomainTheory/DataTypesAsLattices/Lambda/predSet_more.lean)**

@import "../Lambda/predSet_more.lean"
**[DataTypesAsLattices/Lambda/eq_2_7_succ.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_7_succ.lean)**

@import "../Lambda/eq_2_7_succ.lean"
**[DataTypesAsLattices/Lambda/eq_2_7_zero.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_7_zero.lean)**

@import "../Lambda/eq_2_7_zero.lean"
**[DataTypesAsLattices/Lambda/eq_2_7_bot.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_7_bot.lean)**

@import "../Lambda/eq_2_7_bot.lean"
**[DataTypesAsLattices/Lambda/eq_2_7_mix.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_7_mix.lean)**

@import "../Lambda/eq_2_7_mix.lean"
**[DataTypesAsLattices/Lambda/eq_2_7_pos.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_7_pos.lean)**

@import "../Lambda/eq_2_7_pos.lean"
**[DataTypesAsLattices/Lambda/condC.lean](DomainTheory/DataTypesAsLattices/Lambda/condC.lean)**

@import "../Lambda/condC.lean"
**[DataTypesAsLattices/Lambda/graph_const_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Lambda/graph_const_isScottContinuous.lean)**

@import "../Lambda/graph_const_isScottContinuous.lean"
**[DataTypesAsLattices/Lambda/const_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Lambda/const_isScottContinuous.lean)**

@import "../Lambda/const_isScottContinuous.lean"
**[DataTypesAsLattices/Lambda/id_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Lambda/id_isScottContinuous.lean)**

@import "../Lambda/id_isScottContinuous.lean"
**[DataTypesAsLattices/Lambda/eq_2_15.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_15.lean)**

@import "../Lambda/eq_2_15.lean"
**[DataTypesAsLattices/Lambda/topRec.lean](DomainTheory/DataTypesAsLattices/Lambda/topRec.lean)**

@import "../Lambda/topRec.lean"
**[DataTypesAsLattices/Lambda/eq_2_16.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_16.lean)**

@import "../Lambda/eq_2_16.lean"
**[DataTypesAsLattices/Retracts/sUnion_Fixpoints_le_image.lean](DomainTheory/DataTypesAsLattices/Retracts/sUnion_Fixpoints_le_image.lean)**

@import "../Retracts/sUnion_Fixpoints_le_image.lean"
**[DataTypesAsLattices/Retracts/gfpBelow.lean](DomainTheory/DataTypesAsLattices/Retracts/gfpBelow.lean)**

@import "../Retracts/gfpBelow.lean"
**[DataTypesAsLattices/Retracts/iterateFrom.lean](DomainTheory/DataTypesAsLattices/Retracts/iterateFrom.lean)**

@import "../Retracts/iterateFrom.lean"
**[DataTypesAsLattices/Computability/IsComputable.lean](DomainTheory/DataTypesAsLattices/Computability/IsComputable.lean)**

@import "../Computability/IsComputable.lean"
**[DataTypesAsLattices/Continuous/exists_e_cover_finite.lean](DomainTheory/DataTypesAsLattices/Continuous/exists_e_cover_finite.lean)**

@import "../Continuous/exists_e_cover_finite.lean"
**[DataTypesAsLattices/Continuous/theorem_1_1.lean](DomainTheory/DataTypesAsLattices/Continuous/theorem_1_1.lean)**

@import "../Continuous/theorem_1_1.lean"
**[DataTypesAsLattices/FixedPoint/theorem_1_3.lean](DomainTheory/DataTypesAsLattices/FixedPoint/theorem_1_3.lean)**

@import "../FixedPoint/theorem_1_3.lean"
**[DataTypesAsLattices/Lambda/iterateBot_param_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Lambda/iterateBot_param_isScottContinuous.lean)**

@import "../Lambda/iterateBot_param_isScottContinuous.lean"
**[DataTypesAsLattices/Lambda/fix_param_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Lambda/fix_param_isScottContinuous.lean)**

@import "../Lambda/fix_param_isScottContinuous.lean"
**[DataTypesAsLattices/FixedPoint/chain_lemma.lean](DomainTheory/DataTypesAsLattices/FixedPoint/chain_lemma.lean)**

@import "../FixedPoint/chain_lemma.lean"
**[DataTypesAsLattices/Retracts/lfpAbove.lean](DomainTheory/DataTypesAsLattices/Retracts/lfpAbove.lean)**

@import "../Retracts/lfpAbove.lean"
**[DataTypesAsLattices/FixedPoint/iterateBot_mono.lean](DomainTheory/DataTypesAsLattices/FixedPoint/iterateBot_mono.lean)**

@import "../FixedPoint/iterateBot_mono.lean"
**[DataTypesAsLattices/FixedPoint/theorem_1_4.lean](DomainTheory/DataTypesAsLattices/FixedPoint/theorem_1_4.lean)**

@import "../FixedPoint/theorem_1_4.lean"
**[DataTypesAsLattices/Graph/funOf.lean](DomainTheory/DataTypesAsLattices/Graph/funOf.lean)**

@import "../Graph/funOf.lean"
**[DataTypesAsLattices/Lambda/nestApplyFin.lean](DomainTheory/DataTypesAsLattices/Lambda/nestApplyFin.lean)**

@import "../Lambda/nestApplyFin.lean"
**[DataTypesAsLattices/Lambda/interp.lean](DomainTheory/DataTypesAsLattices/Lambda/interp.lean)**

@import "../Lambda/interp.lean"
**[DataTypesAsLattices/Lambda/Fofg.lean](DomainTheory/DataTypesAsLattices/Lambda/Fofg.lean)**

@import "../Lambda/Fofg.lean"
**[DataTypesAsLattices/Lambda/Scomb.lean](DomainTheory/DataTypesAsLattices/Lambda/Scomb.lean)**

@import "../Lambda/Scomb.lean"
**[DataTypesAsLattices/Lambda/IsCombinatory.lean](DomainTheory/DataTypesAsLattices/Lambda/IsCombinatory.lean)**

@import "../Lambda/IsCombinatory.lean"
**[DataTypesAsLattices/Lambda/dcondSet.lean](DomainTheory/DataTypesAsLattices/Lambda/dcondSet.lean)**

@import "../Lambda/dcondSet.lean"
**[DataTypesAsLattices/Lambda/dcondSet_more.lean](DomainTheory/DataTypesAsLattices/Lambda/dcondSet_more.lean)**

@import "../Lambda/dcondSet_more.lean"
**[DataTypesAsLattices/Lambda/ofComb.lean](DomainTheory/DataTypesAsLattices/Lambda/ofComb.lean)**

@import "../Lambda/ofComb.lean"
**[DataTypesAsLattices/Lambda/theorem_2_1.lean](DomainTheory/DataTypesAsLattices/Lambda/theorem_2_1.lean)**

@import "../Lambda/theorem_2_1.lean"
**[DataTypesAsLattices/Lambda/diagApp_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Lambda/diagApp_isScottContinuous.lean)**

@import "../Lambda/diagApp_isScottContinuous.lean"
**[DataTypesAsLattices/Lambda/eq_2_9.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_9.lean)**

@import "../Lambda/eq_2_9.lean"
**[DataTypesAsLattices/Lambda/FUN.lean](DomainTheory/DataTypesAsLattices/Lambda/FUN.lean)**

@import "../Lambda/FUN.lean"
**[DataTypesAsLattices/Lambda/eq_2_13.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_13.lean)**

@import "../Lambda/eq_2_13.lean"
**[DataTypesAsLattices/Lambda/eq_2_11.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_11.lean)**

@import "../Lambda/eq_2_11.lean"
**[DataTypesAsLattices/Computability/topRecTerm.lean](DomainTheory/DataTypesAsLattices/Computability/topRecTerm.lean)**

@import "../Computability/topRecTerm.lean"
**[DataTypesAsLattices/Lambda/interStep.lean](DomainTheory/DataTypesAsLattices/Lambda/interStep.lean)**

@import "../Lambda/interStep.lean"
**[DataTypesAsLattices/Lambda/seqFunLt.lean](DomainTheory/DataTypesAsLattices/Lambda/seqFunLt.lean)**

@import "../Lambda/seqFunLt.lean"
**[DataTypesAsLattices/Lambda/mem_seqFunLt.lean](DomainTheory/DataTypesAsLattices/Lambda/mem_seqFunLt.lean)**

@import "../Lambda/mem_seqFunLt.lean"
**[DataTypesAsLattices/Lambda/seqCons.lean](DomainTheory/DataTypesAsLattices/Lambda/seqCons.lean)**

@import "../Lambda/seqCons.lean"
**[DataTypesAsLattices/Lambda/seqFun.lean](DomainTheory/DataTypesAsLattices/Lambda/seqFun.lean)**

@import "../Lambda/seqFun.lean"
**[DataTypesAsLattices/Lambda/seqShift.lean](DomainTheory/DataTypesAsLattices/Lambda/seqShift.lean)**

@import "../Lambda/seqShift.lean"
**[DataTypesAsLattices/Lambda/seqFun_more.lean](DomainTheory/DataTypesAsLattices/Lambda/seqFun_more.lean)**

@import "../Lambda/seqFun_more.lean"
**[DataTypesAsLattices/Computability/LambdaDefinable.lean](DomainTheory/DataTypesAsLattices/Computability/LambdaDefinable.lean)**

@import "../Computability/LambdaDefinable.lean"
**[DataTypesAsLattices/Computability/combinatory_isLambdaDefinable.lean](DomainTheory/DataTypesAsLattices/Computability/combinatory_isLambdaDefinable.lean)**

@import "../Computability/combinatory_isLambdaDefinable.lean"
**[DataTypesAsLattices/Computability/Realizes.lean](DomainTheory/DataTypesAsLattices/Computability/Realizes.lean)**

@import "../Computability/Realizes.lean"
**[DataTypesAsLattices/Retracts/typed.lean](DomainTheory/DataTypesAsLattices/Retracts/typed.lean)**

@import "../Retracts/typed.lean"
**[DataTypesAsLattices/Retracts/dcondSet_bool_idem.lean](DomainTheory/DataTypesAsLattices/Retracts/dcondSet_bool_idem.lean)**

@import "../Retracts/dcondSet_bool_idem.lean"
**[DataTypesAsLattices/Computability/addStepC.lean](DomainTheory/DataTypesAsLattices/Computability/addStepC.lean)**

@import "../Computability/addStepC.lean"
**[DataTypesAsLattices/Graph/Basic/notation3.lean](DomainTheory/DataTypesAsLattices/Graph/Basic/notation3.lean)**

@import "../Graph/Basic/notation3.lean"
**[DataTypesAsLattices/Graph/funOf_more.lean](DomainTheory/DataTypesAsLattices/Graph/funOf_more.lean)**

@import "../Graph/funOf_more.lean"
**[DataTypesAsLattices/Retracts/IsStrict.lean](DomainTheory/DataTypesAsLattices/Retracts/IsStrict.lean)**

@import "../Retracts/IsStrict.lean"
**[DataTypesAsLattices/Retracts/dcondSet_same_ofNat.lean](DomainTheory/DataTypesAsLattices/Retracts/dcondSet_same_ofNat.lean)**

@import "../Retracts/dcondSet_same_ofNat.lean"
**[DataTypesAsLattices/Retracts/funOf_botElem.lean](DomainTheory/DataTypesAsLattices/Retracts/funOf_botElem.lean)**

@import "../Retracts/funOf_botElem.lean"
**[DataTypesAsLattices/Retracts/theorem_4_1.lean](DomainTheory/DataTypesAsLattices/Retracts/theorem_4_1.lean)**

@import "../Retracts/theorem_4_1.lean"
**[DataTypesAsLattices/Retracts/fixpointsCompleteLattice.lean](DomainTheory/DataTypesAsLattices/Retracts/fixpointsCompleteLattice.lean)**

@import "../Retracts/fixpointsCompleteLattice.lean"
**[DataTypesAsLattices/Retracts/BasicInst36.lean](DomainTheory/DataTypesAsLattices/Retracts/BasicInst36.lean)**

@import "../Retracts/BasicInst36.lean"
**[DataTypesAsLattices/Computability/Realizes2.lean](DomainTheory/DataTypesAsLattices/Computability/Realizes2.lean)**

@import "../Computability/Realizes2.lean"
**[DataTypesAsLattices/Computability/mem_Scomb_iff.lean](DomainTheory/DataTypesAsLattices/Computability/mem_Scomb_iff.lean)**

@import "../Computability/mem_Scomb_iff.lean"
**[DataTypesAsLattices/Computability/mem_condC_iff.lean](DomainTheory/DataTypesAsLattices/Computability/mem_condC_iff.lean)**

@import "../Computability/mem_condC_iff.lean"
**[DataTypesAsLattices/Graph/mem_graph.lean](DomainTheory/DataTypesAsLattices/Graph/mem_graph.lean)**

@import "../Graph/mem_graph.lean"
**[DataTypesAsLattices/Graph/theorem_1_2.lean](DomainTheory/DataTypesAsLattices/Graph/theorem_1_2.lean)**

@import "../Graph/theorem_1_2.lean"
**[DataTypesAsLattices/Graph/beta.lean](DomainTheory/DataTypesAsLattices/Graph/beta.lean)**

@import "../Graph/beta.lean"
**[DataTypesAsLattices/Lambda/curry2.lean](DomainTheory/DataTypesAsLattices/Lambda/curry2.lean)**

@import "../Lambda/curry2.lean"
**[DataTypesAsLattices/Lambda/Scomb_more.lean](DomainTheory/DataTypesAsLattices/Lambda/Scomb_more.lean)**

@import "../Lambda/Scomb_more.lean"
**[DataTypesAsLattices/Lambda/curryFin.lean](DomainTheory/DataTypesAsLattices/Lambda/curryFin.lean)**

@import "../Lambda/curryFin.lean"
**[DataTypesAsLattices/Lambda/termShift.lean](DomainTheory/DataTypesAsLattices/Lambda/termShift.lean)**

@import "../Lambda/termShift.lean"
**[DataTypesAsLattices/Lambda/condC_more.lean](DomainTheory/DataTypesAsLattices/Lambda/condC_more.lean)**

@import "../Lambda/condC_more.lean"
**[DataTypesAsLattices/Lambda/curry3.lean](DomainTheory/DataTypesAsLattices/Lambda/curry3.lean)**

@import "../Lambda/curry3.lean"
**[DataTypesAsLattices/Lambda/sucC_more.lean](DomainTheory/DataTypesAsLattices/Lambda/sucC_more.lean)**

@import "../Lambda/sucC_more.lean"
**[DataTypesAsLattices/Lambda/predC_more.lean](DomainTheory/DataTypesAsLattices/Lambda/predC_more.lean)**

@import "../Lambda/predC_more.lean"
**[DataTypesAsLattices/Lambda/Kcomb_more.lean](DomainTheory/DataTypesAsLattices/Lambda/Kcomb_more.lean)**

@import "../Lambda/Kcomb_more.lean"
**[DataTypesAsLattices/Lambda/SKK_eq_I.lean](DomainTheory/DataTypesAsLattices/Lambda/SKK_eq_I.lean)**

@import "../Lambda/SKK_eq_I.lean"
**[DataTypesAsLattices/Lambda/abs.lean](DomainTheory/DataTypesAsLattices/Lambda/abs.lean)**

@import "../Lambda/abs.lean"
**[DataTypesAsLattices/Lambda/erase.lean](DomainTheory/DataTypesAsLattices/Lambda/erase.lean)**

@import "../Lambda/erase.lean"
**[DataTypesAsLattices/Lambda/ofNat_more.lean](DomainTheory/DataTypesAsLattices/Lambda/ofNat_more.lean)**

@import "../Lambda/ofNat_more.lean"
**[DataTypesAsLattices/Lambda/theorem_2_2.lean](DomainTheory/DataTypesAsLattices/Lambda/theorem_2_2.lean)**

@import "../Lambda/theorem_2_2.lean"
**[DataTypesAsLattices/Lambda/primRecStepTerm.lean](DomainTheory/DataTypesAsLattices/Lambda/primRecStepTerm.lean)**

@import "../Lambda/primRecStepTerm.lean"
**[DataTypesAsLattices/Lambda/primRecStep.lean](DomainTheory/DataTypesAsLattices/Lambda/primRecStep.lean)**

@import "../Lambda/primRecStep.lean"
**[DataTypesAsLattices/Lambda/theorem_2_3.lean](DomainTheory/DataTypesAsLattices/Lambda/theorem_2_3.lean)**

@import "../Lambda/theorem_2_3.lean"
**[DataTypesAsLattices/Lambda/theorem_2_4.lean](DomainTheory/DataTypesAsLattices/Lambda/theorem_2_4.lean)**

@import "../Lambda/theorem_2_4.lean"
**[DataTypesAsLattices/Lambda/omegaComb.lean](DomainTheory/DataTypesAsLattices/Lambda/omegaComb.lean)**

@import "../Lambda/omegaComb.lean"
**[DataTypesAsLattices/Lambda/omega_first_recursion.lean](DomainTheory/DataTypesAsLattices/Lambda/omega_first_recursion.lean)**

@import "../Lambda/omega_first_recursion.lean"
**[DataTypesAsLattices/Lambda/Ycomb.lean](DomainTheory/DataTypesAsLattices/Lambda/Ycomb.lean)**

@import "../Lambda/Ycomb.lean"
**[DataTypesAsLattices/Lambda/Yterm.lean](DomainTheory/DataTypesAsLattices/Lambda/Yterm.lean)**

@import "../Lambda/Yterm.lean"
**[DataTypesAsLattices/Lambda/Ycomb_more.lean](DomainTheory/DataTypesAsLattices/Lambda/Ycomb_more.lean)**

@import "../Lambda/Ycomb_more.lean"
**[DataTypesAsLattices/Lambda/theorem_2_5.lean](DomainTheory/DataTypesAsLattices/Lambda/theorem_2_5.lean)**

@import "../Lambda/theorem_2_5.lean"
**[DataTypesAsLattices/Lambda/union_via_cond.lean](DomainTheory/DataTypesAsLattices/Lambda/union_via_cond.lean)**

@import "../Lambda/union_via_cond.lean"
**[DataTypesAsLattices/Lambda/interC.lean](DomainTheory/DataTypesAsLattices/Lambda/interC.lean)**

@import "../Lambda/interC.lean"
**[DataTypesAsLattices/Lambda/eq_2_17.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_17.lean)**

@import "../Lambda/eq_2_17.lean"
**[DataTypesAsLattices/Lambda/eq_2_14.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_14.lean)**

@import "../Lambda/eq_2_14.lean"
**[DataTypesAsLattices/Lambda/seqShift_more.lean](DomainTheory/DataTypesAsLattices/Lambda/seqShift_more.lean)**

@import "../Lambda/seqShift_more.lean"
**[DataTypesAsLattices/Lambda/seqFunLt_more.lean](DomainTheory/DataTypesAsLattices/Lambda/seqFunLt_more.lean)**

@import "../Lambda/seqFunLt_more.lean"
**[DataTypesAsLattices/Lambda/seq2.lean](DomainTheory/DataTypesAsLattices/Lambda/seq2.lean)**

@import "../Lambda/seq2.lean"
**[DataTypesAsLattices/Lambda/eq_2_23_ge.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_23_ge.lean)**

@import "../Lambda/eq_2_23_ge.lean"
**[DataTypesAsLattices/Lambda/eq_2_23_one.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_23_one.lean)**

@import "../Lambda/eq_2_23_one.lean"
**[DataTypesAsLattices/Lambda/eq_2_23_zero.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_23_zero.lean)**

@import "../Lambda/eq_2_23_zero.lean"
**[DataTypesAsLattices/Lambda/eq_2_22.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_22.lean)**

@import "../Lambda/eq_2_22.lean"
**[DataTypesAsLattices/Lambda/dollarStepBody.lean](DomainTheory/DataTypesAsLattices/Lambda/dollarStepBody.lean)**

@import "../Lambda/dollarStepBody.lean"
**[DataTypesAsLattices/Lambda/dollarStep.lean](DomainTheory/DataTypesAsLattices/Lambda/dollarStep.lean)**

@import "../Lambda/dollarStep.lean"
**[DataTypesAsLattices/Lambda/termDollarStepBody.lean](DomainTheory/DataTypesAsLattices/Lambda/termDollarStepBody.lean)**

@import "../Lambda/termDollarStepBody.lean"
**[DataTypesAsLattices/Lambda/termDollarStep.lean](DomainTheory/DataTypesAsLattices/Lambda/termDollarStep.lean)**

@import "../Lambda/termDollarStep.lean"
**[DataTypesAsLattices/Lambda/dollarStepTerm.lean](DomainTheory/DataTypesAsLattices/Lambda/dollarStepTerm.lean)**

@import "../Lambda/dollarStepTerm.lean"
**[DataTypesAsLattices/Lambda/dollarC.lean](DomainTheory/DataTypesAsLattices/Lambda/dollarC.lean)**

@import "../Lambda/dollarC.lean"
**[DataTypesAsLattices/Lambda/eq_2_24.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_24.lean)**

@import "../Lambda/eq_2_24.lean"
**[DataTypesAsLattices/Lambda/eq_2_25.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_25.lean)**

@import "../Lambda/eq_2_25.lean"
**[DataTypesAsLattices/Lambda/primRecVal.lean](DomainTheory/DataTypesAsLattices/Lambda/primRecVal.lean)**

@import "../Lambda/primRecVal.lean"
**[DataTypesAsLattices/Lambda/primRecHat.lean](DomainTheory/DataTypesAsLattices/Lambda/primRecHat.lean)**

@import "../Lambda/primRecHat.lean"
**[DataTypesAsLattices/Computability/primRecVal_add.lean](DomainTheory/DataTypesAsLattices/Computability/primRecVal_add.lean)**

@import "../Computability/primRecVal_add.lean"
**[DataTypesAsLattices/Lambda/eq_2_27.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_27.lean)**

@import "../Lambda/eq_2_27.lean"
**[DataTypesAsLattices/Computability/primRecComb.lean](DomainTheory/DataTypesAsLattices/Computability/primRecComb.lean)**

@import "../Computability/primRecComb.lean"
**[DataTypesAsLattices/Lambda/Ymap.lean](DomainTheory/DataTypesAsLattices/Lambda/Ymap.lean)**

@import "../Lambda/Ymap.lean"
**[DataTypesAsLattices/Lambda/eq_2_28.lean](DomainTheory/DataTypesAsLattices/Lambda/eq_2_28.lean)**

@import "../Lambda/eq_2_28.lean"
**[DataTypesAsLattices/Retracts/sndC.lean](DomainTheory/DataTypesAsLattices/Retracts/sndC.lean)**

@import "../Retracts/sndC.lean"
**[DataTypesAsLattices/Retracts/intF.lean](DomainTheory/DataTypesAsLattices/Retracts/intF.lean)**

@import "../Retracts/intF.lean"
**[DataTypesAsLattices/Retracts/pairSeq.lean](DomainTheory/DataTypesAsLattices/Retracts/pairSeq.lean)**

@import "../Retracts/pairSeq.lean"
**[DataTypesAsLattices/Retracts/comp.lean](DomainTheory/DataTypesAsLattices/Retracts/comp.lean)**

@import "../Retracts/comp.lean"
**[DataTypesAsLattices/Retracts/arrowR.lean](DomainTheory/DataTypesAsLattices/Retracts/arrowR.lean)**

@import "../Retracts/arrowR.lean"
**[DataTypesAsLattices/Retracts/eq_4_11.lean](DomainTheory/DataTypesAsLattices/Retracts/eq_4_11.lean)**

@import "../Retracts/eq_4_11.lean"
**[DataTypesAsLattices/Computability/ComputableFin.lean](DomainTheory/DataTypesAsLattices/Computability/ComputableFin.lean)**

@import "../Computability/ComputableFin.lean"
**[DataTypesAsLattices/Computability/SK_comp.lean](DomainTheory/DataTypesAsLattices/Computability/SK_comp.lean)**

@import "../Computability/SK_comp.lean"
**[DataTypesAsLattices/Computability/primRecZeroC.lean](DomainTheory/DataTypesAsLattices/Computability/primRecZeroC.lean)**

@import "../Computability/primRecZeroC.lean"
**[DataTypesAsLattices/Computability/addC.lean](DomainTheory/DataTypesAsLattices/Computability/addC.lean)**

@import "../Computability/addC.lean"
**[DataTypesAsLattices/Computability/primRecVal_mul.lean](DomainTheory/DataTypesAsLattices/Computability/primRecVal_mul.lean)**

@import "../Computability/primRecVal_mul.lean"
**[DataTypesAsLattices/Computability/botElem_combinatory.lean](DomainTheory/DataTypesAsLattices/Computability/botElem_combinatory.lean)**

@import "../Computability/botElem_combinatory.lean"
**[DataTypesAsLattices/Computability/primRecOpEnv.lean](DomainTheory/DataTypesAsLattices/Computability/primRecOpEnv.lean)**

@import "../Computability/primRecOpEnv.lean"
**[DataTypesAsLattices/Computability/primRecOpC.lean](DomainTheory/DataTypesAsLattices/Computability/primRecOpC.lean)**

@import "../Computability/primRecOpC.lean"
**[DataTypesAsLattices/Computability/safePredC.lean](DomainTheory/DataTypesAsLattices/Computability/safePredC.lean)**

@import "../Computability/safePredC.lean"
**[DataTypesAsLattices/Computability/subStepC.lean](DomainTheory/DataTypesAsLattices/Computability/subStepC.lean)**

@import "../Computability/subStepC.lean"
**[DataTypesAsLattices/Computability/primRecVal_sub.lean](DomainTheory/DataTypesAsLattices/Computability/primRecVal_sub.lean)**

@import "../Computability/primRecVal_sub.lean"
**[DataTypesAsLattices/Enumeration/unionTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionTerm.lean)**

@import "../Enumeration/unionTerm.lean"
**[DataTypesAsLattices/Enumeration/unionOperator_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionOperator_combinatory.lean)**

@import "../Enumeration/unionOperator_combinatory.lean"
**[DataTypesAsLattices/Retracts/Retract.lean](DomainTheory/DataTypesAsLattices/Retracts/Retract.lean)**

@import "../Retracts/Retract.lean"
**[DataTypesAsLattices/Retracts/funRetract.lean](DomainTheory/DataTypesAsLattices/Retracts/funRetract.lean)**

@import "../Retracts/funRetract.lean"
**[DataTypesAsLattices/Retracts/intR.lean](DomainTheory/DataTypesAsLattices/Retracts/intR.lean)**

@import "../Retracts/intR.lean"
**[DataTypesAsLattices/Retracts/retract_interpolation.lean](DomainTheory/DataTypesAsLattices/Retracts/retract_interpolation.lean)**

@import "../Retracts/retract_interpolation.lean"
**[DataTypesAsLattices/Retracts/boolR.lean](DomainTheory/DataTypesAsLattices/Retracts/boolR.lean)**

@import "../Retracts/boolR.lean"
**[DataTypesAsLattices/Retracts/Icomb.lean](DomainTheory/DataTypesAsLattices/Retracts/Icomb.lean)**

@import "../Retracts/Icomb.lean"
**[DataTypesAsLattices/Retracts/retractLe.lean](DomainTheory/DataTypesAsLattices/Retracts/retractLe.lean)**

@import "../Retracts/retractLe.lean"
**[DataTypesAsLattices/Closures/Closure.lean](DomainTheory/DataTypesAsLattices/Closures/Closure.lean)**

@import "../Closures/Closure.lean"
**[DataTypesAsLattices/Closures/Icomb_isClosure.lean](DomainTheory/DataTypesAsLattices/Closures/Icomb_isClosure.lean)**

@import "../Closures/Icomb_isClosure.lean"
**[DataTypesAsLattices/Retracts/retract_app.lean](DomainTheory/DataTypesAsLattices/Retracts/retract_app.lean)**

@import "../Retracts/retract_app.lean"
**[DataTypesAsLattices/Computability/REPredu2eand.lean](DomainTheory/DataTypesAsLattices/Computability/REPredu2eand.lean)**

@import "../Computability/REPredu2eand.lean"
**[DataTypesAsLattices/Computability/REPredu2ecomp.lean](DomainTheory/DataTypesAsLattices/Computability/REPredu2ecomp.lean)**

@import "../Computability/REPredu2ecomp.lean"
**[DataTypesAsLattices/Computability/REPredu2eexists.lean](DomainTheory/DataTypesAsLattices/Computability/REPredu2eexists.lean)**

@import "../Computability/REPredu2eexists.lean"
**[DataTypesAsLattices/Computability/mulC.lean](DomainTheory/DataTypesAsLattices/Computability/mulC.lean)**

@import "../Computability/mulC.lean"
**[DataTypesAsLattices/Computability/primrecPred_bool.lean](DomainTheory/DataTypesAsLattices/Computability/primrecPred_bool.lean)**

@import "../Computability/primrecPred_bool.lean"
**[DataTypesAsLattices/Computability/primrec_enumFun.lean](DomainTheory/DataTypesAsLattices/Computability/primrec_enumFun.lean)**

@import "../Computability/primrec_enumFun.lean"
**[DataTypesAsLattices/Computability/primrec_pack4_proj1.lean](DomainTheory/DataTypesAsLattices/Computability/primrec_pack4_proj1.lean)**

@import "../Computability/primrec_pack4_proj1.lean"
**[DataTypesAsLattices/Computability/primrec_pack4_proj2.lean](DomainTheory/DataTypesAsLattices/Computability/primrec_pack4_proj2.lean)**

@import "../Computability/primrec_pack4_proj2.lean"
**[DataTypesAsLattices/Computability/primrec_pack4_proj3.lean](DomainTheory/DataTypesAsLattices/Computability/primrec_pack4_proj3.lean)**

@import "../Computability/primrec_pack4_proj3.lean"
**[DataTypesAsLattices/Computability/primrec_pack4_proj4.lean](DomainTheory/DataTypesAsLattices/Computability/primrec_pack4_proj4.lean)**

@import "../Computability/primrec_pack4_proj4.lean"
**[DataTypesAsLattices/Computability/primrec_pair.lean](DomainTheory/DataTypesAsLattices/Computability/primrec_pair.lean)**

@import "../Computability/primrec_pair.lean"
**[DataTypesAsLattices/Computability/IsREu2epair_mem.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2epair_mem.lean)**

@import "../Computability/IsREu2epair_mem.lean"
**[DataTypesAsLattices/Computability/primrecPred_Scomb_eq.lean](DomainTheory/DataTypesAsLattices/Computability/primrecPred_Scomb_eq.lean)**

@import "../Computability/primrecPred_Scomb_eq.lean"
**[DataTypesAsLattices/Computability/primrecPred_eq_scott_pair.lean](DomainTheory/DataTypesAsLattices/Computability/primrecPred_eq_scott_pair.lean)**

@import "../Computability/primrecPred_eq_scott_pair.lean"
**[DataTypesAsLattices/Computability/IsREu2egraph_of_re.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2egraph_of_re.lean)**

@import "../Computability/IsREu2egraph_of_re.lean"
**[DataTypesAsLattices/Computability/primrec_twoPow.lean](DomainTheory/DataTypesAsLattices/Computability/primrec_twoPow.lean)**

@import "../Computability/primrec_twoPow.lean"
**[DataTypesAsLattices/Computability/primrec_testBit.lean](DomainTheory/DataTypesAsLattices/Computability/primrec_testBit.lean)**

@import "../Computability/primrec_testBit.lean"
**[DataTypesAsLattices/Computability/IsREu2eKcomb.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2eKcomb.lean)**

@import "../Computability/IsREu2eKcomb.lean"
**[DataTypesAsLattices/Computability/IsREu2econdC.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2econdC.lean)**

@import "../Computability/IsREu2econdC.lean"
**[DataTypesAsLattices/Computability/subC.lean](DomainTheory/DataTypesAsLattices/Computability/subC.lean)**

@import "../Computability/subC.lean"
**[DataTypesAsLattices/Computability/topElem_combinatory.lean](DomainTheory/DataTypesAsLattices/Computability/topElem_combinatory.lean)**

@import "../Computability/topElem_combinatory.lean"
**[DataTypesAsLattices/Computability/enumRangeC.lean](DomainTheory/DataTypesAsLattices/Computability/enumRangeC.lean)**

@import "../Computability/enumRangeC.lean"
**[DataTypesAsLattices/Enumeration/bot_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/bot_combinatory.lean)**

@import "../Enumeration/bot_combinatory.lean"
**[DataTypesAsLattices/Retracts/RetractInverseLimit.lean](DomainTheory/DataTypesAsLattices/Retracts/RetractInverseLimit.lean)**

@import "../Retracts/RetractInverseLimit.lean"
**[DataTypesAsLattices/Retracts/BasicInst55.lean](DomainTheory/DataTypesAsLattices/Retracts/BasicInst55.lean)**

@import "../Retracts/BasicInst55.lean"
**[DataTypesAsLattices/Retracts/bot_retractLe.lean](DomainTheory/DataTypesAsLattices/Retracts/bot_retractLe.lean)**

@import "../Retracts/bot_retractLe.lean"
**[DataTypesAsLattices/Retracts/curryC.lean](DomainTheory/DataTypesAsLattices/Retracts/curryC.lean)**

@import "../Retracts/curryC.lean"
**[DataTypesAsLattices/Retracts/diagC.lean](DomainTheory/DataTypesAsLattices/Retracts/diagC.lean)**

@import "../Retracts/diagC.lean"
**[DataTypesAsLattices/Retracts/directed_sUnion_fixed.lean](DomainTheory/DataTypesAsLattices/Retracts/directed_sUnion_fixed.lean)**

@import "../Retracts/directed_sUnion_fixed.lean"
**[DataTypesAsLattices/Retracts/sSup_fixed_eq_sUnion.lean](DomainTheory/DataTypesAsLattices/Retracts/sSup_fixed_eq_sUnion.lean)**

@import "../Retracts/sSup_fixed_eq_sUnion.lean"
**[DataTypesAsLattices/Retracts/retractBasis.lean](DomainTheory/DataTypesAsLattices/Retracts/retractBasis.lean)**

@import "../Retracts/retractBasis.lean"
**[DataTypesAsLattices/Retracts/evalC.lean](DomainTheory/DataTypesAsLattices/Retracts/evalC.lean)**

@import "../Retracts/evalC.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_mono.lean](DomainTheory/DataTypesAsLattices/Retracts/inverseLimit_mono.lean)**

@import "../Retracts/inverseLimit_mono.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_chain.lean](DomainTheory/DataTypesAsLattices/Retracts/inverseLimit_chain.lean)**

@import "../Retracts/inverseLimit_chain.lean"
**[DataTypesAsLattices/Computability/IsREu2egraph_of_primrecRel.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2egraph_of_primrecRel.lean)**

@import "../Computability/IsREu2egraph_of_primrecRel.lean"
**[DataTypesAsLattices/Computability/IsREu2epredC.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2epredC.lean)**

@import "../Computability/IsREu2epredC.lean"
**[DataTypesAsLattices/Computability/IsREu2esucC.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2esucC.lean)**

@import "../Computability/IsREu2esucC.lean"
**[DataTypesAsLattices/Computability/IsREu2enumeral.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2enumeral.lean)**

@import "../Computability/IsREu2enumeral.lean"
**[DataTypesAsLattices/Computability/IsREu2ezeroC.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2ezeroC.lean)**

@import "../Computability/IsREu2ezeroC.lean"
**[DataTypesAsLattices/Computability/composeC.lean](DomainTheory/DataTypesAsLattices/Computability/composeC.lean)**

@import "../Computability/composeC.lean"
**[DataTypesAsLattices/Computability/constComb.lean](DomainTheory/DataTypesAsLattices/Computability/constComb.lean)**

@import "../Computability/constComb.lean"
**[DataTypesAsLattices/Computability/isZeroC.lean](DomainTheory/DataTypesAsLattices/Computability/isZeroC.lean)**

@import "../Computability/isZeroC.lean"
**[DataTypesAsLattices/Computability/leC.lean](DomainTheory/DataTypesAsLattices/Computability/leC.lean)**

@import "../Computability/leC.lean"
**[DataTypesAsLattices/Computability/sqrtEnv.lean](DomainTheory/DataTypesAsLattices/Computability/sqrtEnv.lean)**

@import "../Computability/sqrtEnv.lean"
**[DataTypesAsLattices/Computability/sqrtStepC.lean](DomainTheory/DataTypesAsLattices/Computability/sqrtStepC.lean)**

@import "../Computability/sqrtStepC.lean"
**[DataTypesAsLattices/Computability/primRecVal_sqrt.lean](DomainTheory/DataTypesAsLattices/Computability/primRecVal_sqrt.lean)**

@import "../Computability/primRecVal_sqrt.lean"
**[DataTypesAsLattices/Computability/primrecPred_common_stage.lean](DomainTheory/DataTypesAsLattices/Computability/primrecPred_common_stage.lean)**

@import "../Computability/primrecPred_common_stage.lean"
**[DataTypesAsLattices/Computability/IsREu2eeSubset.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2eeSubset.lean)**

@import "../Computability/IsREu2eeSubset.lean"
**[DataTypesAsLattices/Computability/IsREu2efunOf.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2efunOf.lean)**

@import "../Computability/IsREu2efunOf.lean"
**[DataTypesAsLattices/Computability/sqrtC.lean](DomainTheory/DataTypesAsLattices/Computability/sqrtC.lean)**

@import "../Computability/sqrtC.lean"
**[DataTypesAsLattices/Computability/unpairEnv.lean](DomainTheory/DataTypesAsLattices/Computability/unpairEnv.lean)**

@import "../Computability/unpairEnv.lean"
**[DataTypesAsLattices/Computability/unpairFstC.lean](DomainTheory/DataTypesAsLattices/Computability/unpairFstC.lean)**

@import "../Computability/unpairFstC.lean"
**[DataTypesAsLattices/Computability/unpairSndC.lean](DomainTheory/DataTypesAsLattices/Computability/unpairSndC.lean)**

@import "../Computability/unpairSndC.lean"
**[DataTypesAsLattices/Enumeration/RE.lean](DomainTheory/DataTypesAsLattices/Enumeration/RE.lean)**

@import "../Enumeration/RE.lean"
**[DataTypesAsLattices/Computability/mem_funOf_e_iff.lean](DomainTheory/DataTypesAsLattices/Computability/mem_funOf_e_iff.lean)**

@import "../Computability/mem_funOf_e_iff.lean"
**[DataTypesAsLattices/Enumeration/sucC_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/sucC_zero.lean)**

@import "../Enumeration/sucC_zero.lean"
**[DataTypesAsLattices/Computability/arithEnv.lean](DomainTheory/DataTypesAsLattices/Computability/arithEnv.lean)**

@import "../Computability/arithEnv.lean"
**[DataTypesAsLattices/Computability/pairComb.lean](DomainTheory/DataTypesAsLattices/Computability/pairComb.lean)**

@import "../Computability/pairComb.lean"
**[DataTypesAsLattices/Computability/pairRealizer.lean](DomainTheory/DataTypesAsLattices/Computability/pairRealizer.lean)**

@import "../Computability/pairRealizer.lean"
**[DataTypesAsLattices/Computability/precEnv.lean](DomainTheory/DataTypesAsLattices/Computability/precEnv.lean)**

@import "../Computability/precEnv.lean"
**[DataTypesAsLattices/Computability/precC.lean](DomainTheory/DataTypesAsLattices/Computability/precC.lean)**

@import "../Computability/precC.lean"
**[DataTypesAsLattices/Computability/primrec_realized.lean](DomainTheory/DataTypesAsLattices/Computability/primrec_realized.lean)**

@import "../Computability/primrec_realized.lean"
**[DataTypesAsLattices/Computability/IsREu2ecombinatory.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2ecombinatory.lean)**

@import "../Computability/IsREu2ecombinatory.lean"
**[DataTypesAsLattices/Computability/primrecRel_eSubset.lean](DomainTheory/DataTypesAsLattices/Computability/primrecRel_eSubset.lean)**

@import "../Computability/primrecRel_eSubset.lean"
**[DataTypesAsLattices/Computability/primrecRel_mem_funOf_e.lean](DomainTheory/DataTypesAsLattices/Computability/primrecRel_mem_funOf_e.lean)**

@import "../Computability/primrecRel_mem_funOf_e.lean"
**[DataTypesAsLattices/Computability/primrecRel_Scomb_bit.lean](DomainTheory/DataTypesAsLattices/Computability/primrecRel_Scomb_bit.lean)**

@import "../Computability/primrecRel_Scomb_bit.lean"
**[DataTypesAsLattices/Computability/primrecPred_Scomb_subset.lean](DomainTheory/DataTypesAsLattices/Computability/primrecPred_Scomb_subset.lean)**

@import "../Computability/primrecPred_Scomb_subset.lean"
**[DataTypesAsLattices/Computability/primrecRel_Scomb_app.lean](DomainTheory/DataTypesAsLattices/Computability/primrecRel_Scomb_app.lean)**

@import "../Computability/primrecRel_Scomb_app.lean"
**[DataTypesAsLattices/Computability/rePred_Scomb_nested.lean](DomainTheory/DataTypesAsLattices/Computability/rePred_Scomb_nested.lean)**

@import "../Computability/rePred_Scomb_nested.lean"
**[DataTypesAsLattices/Computability/IsREu2eScomb.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2eScomb.lean)**

@import "../Computability/IsREu2eScomb.lean"
**[DataTypesAsLattices/Computability/combinatory_isRE.lean](DomainTheory/DataTypesAsLattices/Computability/combinatory_isRE.lean)**

@import "../Computability/combinatory_isRE.lean"
**[DataTypesAsLattices/Computability/IsREu2eiff_combinatory.lean](DomainTheory/DataTypesAsLattices/Computability/IsREu2eiff_combinatory.lean)**

@import "../Computability/IsREu2eiff_combinatory.lean"
**[DataTypesAsLattices/Classification/BooleanMemE.lean](DomainTheory/DataTypesAsLattices/Classification/BooleanMemE.lean)**

@import "BooleanMemE.lean"
**[DataTypesAsLattices/Classification/IsBdelta.lean](DomainTheory/DataTypesAsLattices/Classification/IsBdelta.lean)**

@import "IsBdelta.lean"
**[DataTypesAsLattices/Classification/IsFcapG.lean](DomainTheory/DataTypesAsLattices/Classification/IsFcapG.lean)**

@import "IsFcapG.lean"
**[DataTypesAsLattices/Classification/ScottB.lean](DomainTheory/DataTypesAsLattices/Classification/ScottB.lean)**

@import "ScottB.lean"
**[DataTypesAsLattices/Classification/ThreeValued.lean](DomainTheory/DataTypesAsLattices/Classification/ThreeValued.lean)**

@import "ThreeValued.lean"
**[DataTypesAsLattices/Classification/charOpen.lean](DomainTheory/DataTypesAsLattices/Classification/charOpen.lean)**

@import "charOpen.lean"
**[DataTypesAsLattices/Classification/charTop.lean](DomainTheory/DataTypesAsLattices/Classification/charTop.lean)**

@import "charTop.lean"
**[DataTypesAsLattices/Classification/closedToZero.lean](DomainTheory/DataTypesAsLattices/Classification/closedToZero.lean)**

@import "closedToZero.lean"
**[DataTypesAsLattices/Classification/evenPart.lean](DomainTheory/DataTypesAsLattices/Classification/evenPart.lean)**

@import "evenPart.lean"
**[DataTypesAsLattices/Classification/oddEvenPack.lean](DomainTheory/DataTypesAsLattices/Classification/oddEvenPack.lean)**

@import "oddEvenPack.lean"
**[DataTypesAsLattices/Classification/oddPart.lean](DomainTheory/DataTypesAsLattices/Classification/oddPart.lean)**

@import "oddPart.lean"
**[DataTypesAsLattices/Classification/pairIndexed.lean](DomainTheory/DataTypesAsLattices/Classification/pairIndexed.lean)**

@import "pairIndexed.lean"
**[DataTypesAsLattices/Classification/typicalBdelta.lean](DomainTheory/DataTypesAsLattices/Classification/typicalBdelta.lean)**

@import "typicalBdelta.lean"
**[DataTypesAsLattices/Classification/uvU.lean](DomainTheory/DataTypesAsLattices/Classification/uvU.lean)**

@import "uvU.lean"
**[DataTypesAsLattices/Classification/uvV.lean](DomainTheory/DataTypesAsLattices/Classification/uvV.lean)**

@import "uvV.lean"
**[DataTypesAsLattices/Classification/zeroPrime.lean](DomainTheory/DataTypesAsLattices/Classification/zeroPrime.lean)**

@import "zeroPrime.lean"
**[DataTypesAsLattices/Classification/Basic.lean](DomainTheory/DataTypesAsLattices/Classification/Basic.lean)**

@import "Basic.lean"
**[DataTypesAsLattices/Classification/IsScottGdelta.lean](DomainTheory/DataTypesAsLattices/Classification/IsScottGdelta.lean)**

@import "IsScottGdelta.lean"
**[DataTypesAsLattices/Classification/IsFcapGdelta.lean](DomainTheory/DataTypesAsLattices/Classification/IsFcapGdelta.lean)**

@import "IsFcapGdelta.lean"
**[DataTypesAsLattices/Classification/ScottF.lean](DomainTheory/DataTypesAsLattices/Classification/ScottF.lean)**

@import "ScottF.lean"
**[DataTypesAsLattices/Classification/fcapGdeltaPack.lean](DomainTheory/DataTypesAsLattices/Classification/fcapGdeltaPack.lean)**

@import "fcapGdeltaPack.lean"
**[DataTypesAsLattices/Classification/zero_not_mem_succSet_top.lean](DomainTheory/DataTypesAsLattices/Classification/zero_not_mem_succSet_top.lean)**

@import "zero_not_mem_succSet_top.lean"
**[DataTypesAsLattices/Classification/fcapGdeltaPack_eq.lean](DomainTheory/DataTypesAsLattices/Classification/fcapGdeltaPack_eq.lean)**

@import "fcapGdeltaPack_eq.lean"
**[DataTypesAsLattices/Classification/fcapGdeltaPack_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Classification/fcapGdeltaPack_isScottContinuous.lean)**

@import "fcapGdeltaPack_isScottContinuous.lean"
**[DataTypesAsLattices/Classification/oddEvenPack_eq_zero.lean](DomainTheory/DataTypesAsLattices/Classification/oddEvenPack_eq_zero.lean)**

@import "oddEvenPack_eq_zero.lean"
**[DataTypesAsLattices/Classification/pairIndexed_eq_top.lean](DomainTheory/DataTypesAsLattices/Classification/pairIndexed_eq_top.lean)**

@import "pairIndexed_eq_top.lean"
**[DataTypesAsLattices/Classification/theorem_6_1.lean](DomainTheory/DataTypesAsLattices/Classification/theorem_6_1.lean)**

@import "theorem_6_1.lean"
**[DataTypesAsLattices/Classification/theorem_6_2.lean](DomainTheory/DataTypesAsLattices/Classification/theorem_6_2.lean)**

@import "theorem_6_2.lean"
**[DataTypesAsLattices/Classification/theorem_6_3.lean](DomainTheory/DataTypesAsLattices/Classification/theorem_6_3.lean)**

@import "theorem_6_3.lean"
**[DataTypesAsLattices/Classification/theorem_6_4.lean](DomainTheory/DataTypesAsLattices/Classification/theorem_6_4.lean)**

@import "theorem_6_4.lean"
**[DataTypesAsLattices/Classification/theorem_6_5.lean](DomainTheory/DataTypesAsLattices/Classification/theorem_6_5.lean)**

@import "theorem_6_5.lean"
**[DataTypesAsLattices/Closures/Vapply.lean](DomainTheory/DataTypesAsLattices/Closures/Vapply.lean)**

@import "../Closures/Vapply.lean"
**[DataTypesAsLattices/Closures/eq_5_1.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_1.lean)**

@import "../Closures/eq_5_1.lean"
**[DataTypesAsLattices/Closures/eq_5_16.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_16.lean)**

@import "../Closures/eq_5_16.lean"
**[DataTypesAsLattices/Closures/eq_5_17.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_17.lean)**

@import "../Closures/eq_5_17.lean"
**[DataTypesAsLattices/Closures/eq_5_18.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_18.lean)**

@import "../Closures/eq_5_18.lean"
**[DataTypesAsLattices/Closures/union_left_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Closures/union_left_isScottContinuous.lean)**

@import "../Closures/union_left_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/union_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Closures/union_right_isScottContinuous.lean)**

@import "../Closures/union_right_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/Vstep.lean](DomainTheory/DataTypesAsLattices/Closures/Vstep.lean)**

@import "../Closures/Vstep.lean"
**[DataTypesAsLattices/Closures/VapplyY.lean](DomainTheory/DataTypesAsLattices/Closures/VapplyY.lean)**

@import "../Closures/VapplyY.lean"
**[DataTypesAsLattices/Closures/Vapply_more.lean](DomainTheory/DataTypesAsLattices/Closures/Vapply_more.lean)**

@import "../Closures/Vapply_more.lean"
**[DataTypesAsLattices/Closures/Vcomb.lean](DomainTheory/DataTypesAsLattices/Closures/Vcomb.lean)**

@import "../Closures/Vcomb.lean"
**[DataTypesAsLattices/Closures/boxTag.lean](DomainTheory/DataTypesAsLattices/Closures/boxTag.lean)**

@import "../Closures/boxTag.lean"
**[DataTypesAsLattices/Closures/closure_expansive.lean](DomainTheory/DataTypesAsLattices/Closures/closure_expansive.lean)**

@import "../Closures/closure_expansive.lean"
**[DataTypesAsLattices/Closures/closureCompact.lean](DomainTheory/DataTypesAsLattices/Closures/closureCompact.lean)**

@import "../Closures/closureCompact.lean"
**[DataTypesAsLattices/Closures/compactFixedBelow.lean](DomainTheory/DataTypesAsLattices/Closures/compactFixedBelow.lean)**

@import "../Closures/compactFixedBelow.lean"
**[DataTypesAsLattices/Closures/representClosure.lean](DomainTheory/DataTypesAsLattices/Closures/representClosure.lean)**

@import "../Closures/representClosure.lean"
**[DataTypesAsLattices/Closures/representClosureCode.lean](DomainTheory/DataTypesAsLattices/Closures/representClosureCode.lean)**

@import "../Closures/representClosureCode.lean"
**[DataTypesAsLattices/Closures/representationEncode_more.lean](DomainTheory/DataTypesAsLattices/Closures/representationEncode_more.lean)**

@import "../Closures/representationEncode_more.lean"
**[DataTypesAsLattices/Closures/representationOrderIso.lean](DomainTheory/DataTypesAsLattices/Closures/representationOrderIso.lean)**

@import "../Closures/representationOrderIso.lean"
**[DataTypesAsLattices/Closures/retractBasis_eq_compactFixedBelow.lean](DomainTheory/DataTypesAsLattices/Closures/retractBasis_eq_compactFixedBelow.lean)**

@import "../Closures/retractBasis_eq_compactFixedBelow.lean"
**[DataTypesAsLattices/Closures/fixed_eq_sSup_compacts.lean](DomainTheory/DataTypesAsLattices/Closures/fixed_eq_sSup_compacts.lean)**

@import "../Closures/fixed_eq_sSup_compacts.lean"
**[DataTypesAsLattices/Closures/squareFst.lean](DomainTheory/DataTypesAsLattices/Closures/squareFst.lean)**

@import "../Closures/squareFst.lean"
**[DataTypesAsLattices/Closures/eq_5_9.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_9.lean)**

@import "../Closures/eq_5_9.lean"
**[DataTypesAsLattices/Closures/squareSnd.lean](DomainTheory/DataTypesAsLattices/Closures/squareSnd.lean)**

@import "../Closures/squareSnd.lean"
**[DataTypesAsLattices/Closures/eq_5_10.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_10.lean)**

@import "../Closures/eq_5_10.lean"
**[DataTypesAsLattices/Closures/squarePair_more.lean](DomainTheory/DataTypesAsLattices/Closures/squarePair_more.lean)**

@import "../Closures/squarePair_more.lean"
**[DataTypesAsLattices/Closures/boxTensor.lean](DomainTheory/DataTypesAsLattices/Closures/boxTensor.lean)**

@import "../Closures/boxTensor.lean"
**[DataTypesAsLattices/Closures/arrowR_diag_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Closures/arrowR_diag_isScottContinuous.lean)**

@import "../Closures/arrowR_diag_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/selfArrowStep.lean](DomainTheory/DataTypesAsLattices/Closures/selfArrowStep.lean)**

@import "../Closures/selfArrowStep.lean"
**[DataTypesAsLattices/Closures/dEq.lean](DomainTheory/DataTypesAsLattices/Closures/dEq.lean)**

@import "../Closures/dEq.lean"
**[DataTypesAsLattices/Closures/compactFixedBelow_more.lean](DomainTheory/DataTypesAsLattices/Closures/compactFixedBelow_more.lean)**

@import "../Closures/compactFixedBelow_more.lean"
**[DataTypesAsLattices/Closures/compact_fixed_iff.lean](DomainTheory/DataTypesAsLattices/Closures/compact_fixed_iff.lean)**

@import "../Closures/compact_fixed_iff.lean"
**[DataTypesAsLattices/Closures/closureRangeCountablyAlgebraic.lean](DomainTheory/DataTypesAsLattices/Closures/closureRangeCountablyAlgebraic.lean)**

@import "../Closures/closureRangeCountablyAlgebraic.lean"
**[DataTypesAsLattices/Closures/theorem_5_5.lean](DomainTheory/DataTypesAsLattices/Closures/theorem_5_5.lean)**

@import "../Closures/theorem_5_5.lean"
**[DataTypesAsLattices/Closures/eq_5_11.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_11.lean)**

@import "../Closures/eq_5_11.lean"
**[DataTypesAsLattices/Closures/Icomb_subset_arrowR.lean](DomainTheory/DataTypesAsLattices/Closures/Icomb_subset_arrowR.lean)**

@import "../Closures/Icomb_subset_arrowR.lean"
**[DataTypesAsLattices/Closures/Icomb_subset_graph.lean](DomainTheory/DataTypesAsLattices/Closures/Icomb_subset_graph.lean)**

@import "../Closures/Icomb_subset_graph.lean"
**[DataTypesAsLattices/Closures/eq_5_8.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_8.lean)**

@import "../Closures/eq_5_8.lean"
**[DataTypesAsLattices/Closures/union_const_left_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Closures/union_const_left_isScottContinuous.lean)**

@import "../Closures/union_const_left_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/boxShift.lean](DomainTheory/DataTypesAsLattices/Closures/boxShift.lean)**

@import "../Closures/boxShift.lean"
**[DataTypesAsLattices/Closures/boxPlus.lean](DomainTheory/DataTypesAsLattices/Closures/boxPlus.lean)**

@import "../Closures/boxPlus.lean"
**[DataTypesAsLattices/Closures/Icomb_subset_boxPlus.lean](DomainTheory/DataTypesAsLattices/Closures/Icomb_subset_boxPlus.lean)**

@import "../Closures/Icomb_subset_boxPlus.lean"
**[DataTypesAsLattices/Closures/Icomb_subset_boxTensor.lean](DomainTheory/DataTypesAsLattices/Closures/Icomb_subset_boxTensor.lean)**

@import "../Closures/Icomb_subset_boxTensor.lean"
**[DataTypesAsLattices/Closures/eq_5_12.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_12.lean)**

@import "../Closures/eq_5_12.lean"
**[DataTypesAsLattices/Closures/eq_5_13.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_13.lean)**

@import "../Closures/eq_5_13.lean"
**[DataTypesAsLattices/Closures/eq_5_14.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_14.lean)**

@import "../Closures/eq_5_14.lean"
**[DataTypesAsLattices/Closures/eq_5_2.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_2.lean)**

@import "../Closures/eq_5_2.lean"
**[DataTypesAsLattices/Closures/theorem_5_4.lean](DomainTheory/DataTypesAsLattices/Closures/theorem_5_4.lean)**

@import "../Closures/theorem_5_4.lean"
**[DataTypesAsLattices/Closures/eq_5_25.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_25.lean)**

@import "../Closures/eq_5_25.lean"
**[DataTypesAsLattices/Closures/openR_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Closures/openR_map_isScottContinuous.lean)**

@import "../Closures/openR_map_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/openR_app.lean](DomainTheory/DataTypesAsLattices/Closures/openR_app.lean)**

@import "../Closures/openR_app.lean"
**[DataTypesAsLattices/Closures/openR_expansive.lean](DomainTheory/DataTypesAsLattices/Closures/openR_expansive.lean)**

@import "../Closures/openR_expansive.lean"
**[DataTypesAsLattices/Closures/theorem_5_1.lean](DomainTheory/DataTypesAsLattices/Closures/theorem_5_1.lean)**

@import "../Closures/theorem_5_1.lean"
**[DataTypesAsLattices/Closures/theorem_5_2.lean](DomainTheory/DataTypesAsLattices/Closures/theorem_5_2.lean)**

@import "../Closures/theorem_5_2.lean"
**[DataTypesAsLattices/Retracts/theorem_4_1_more.lean](DomainTheory/DataTypesAsLattices/Retracts/theorem_4_1_more.lean)**

@import "../Retracts/theorem_4_1_more.lean"
**[DataTypesAsLattices/Retracts/theorem_4_2.lean](DomainTheory/DataTypesAsLattices/Retracts/theorem_4_2.lean)**

@import "../Retracts/theorem_4_2.lean"
