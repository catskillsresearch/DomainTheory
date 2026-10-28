# Total functions and functionality

**Historical note.** Functionality had long been studied in combinatory logic. Hindley, Lercher, and Seldin (1972) is the introduction Scott used. This section is his reading of that theory in $\mathbf{P}\omega$. The connection with the functional interpretation of intuitionistic logic goes back to Curry and Kleene, and Theorem 7.3 is the standard result of that interpretation. Theorem 7.4, that the obvious typing characterizes the iterators, is due to Gordon Plotkin.

**Dependencies.** Inside Functionality, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Functionality.mermaid"

@import "1976_Total_functions_and_functionality.english" {code_block=false}

**[DataTypesAsLattices/Functionality/sigmaJ.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ.lean)**

@import "sigmaJ.lean"
**[DataTypesAsLattices/Functionality/LambTerm.lean](DomainTheory/DataTypesAsLattices/Functionality/LambTerm.lean)**

@import "LambTerm.lean"
**[DataTypesAsLattices/Functionality/RestrictedEquiv.lean](DomainTheory/DataTypesAsLattices/Functionality/RestrictedEquiv.lean)**

@import "RestrictedEquiv.lean"
**[DataTypesAsLattices/Functionality/continuous_on_diag.lean](DomainTheory/DataTypesAsLattices/Functionality/continuous_on_diag.lean)**

@import "continuous_on_diag.lean"
**[DataTypesAsLattices/Functionality/continuous_tuple.lean](DomainTheory/DataTypesAsLattices/Functionality/continuous_tuple.lean)**

@import "continuous_tuple.lean"
**[DataTypesAsLattices/Functionality/arrowR_diag_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/arrowR_diag_isScottContinuous.lean)**

@import "arrowR_diag_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/continuous_nary.lean](DomainTheory/DataTypesAsLattices/Functionality/continuous_nary.lean)**

@import "continuous_nary.lean"
**[DataTypesAsLattices/Functionality/expPayload.lean](DomainTheory/DataTypesAsLattices/Functionality/expPayload.lean)**

@import "expPayload.lean"
**[DataTypesAsLattices/Functionality/expTag.lean](DomainTheory/DataTypesAsLattices/Functionality/expTag.lean)**

@import "expTag.lean"
**[DataTypesAsLattices/Functionality/hApply.lean](DomainTheory/DataTypesAsLattices/Functionality/hApply.lean)**

@import "hApply.lean"
**[DataTypesAsLattices/Functionality/hVar.lean](DomainTheory/DataTypesAsLattices/Functionality/hVar.lean)**

@import "hVar.lean"
**[DataTypesAsLattices/Functionality/inrightC.lean](DomainTheory/DataTypesAsLattices/Functionality/inrightC.lean)**

@import "inrightC.lean"
**[DataTypesAsLattices/Functionality/mem.lean](DomainTheory/DataTypesAsLattices/Functionality/mem.lean)**

@import "mem.lean"
**[DataTypesAsLattices/Functionality/Z.lean](DomainTheory/DataTypesAsLattices/Functionality/Z.lean)**

@import "Z.lean"
**[DataTypesAsLattices/Functionality/eq_7_18_ne.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_7_18_ne.lean)**

@import "eq_7_18_ne.lean"
**[DataTypesAsLattices/Functionality/eq_7_18_eq.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_7_18_eq.lean)**

@import "eq_7_18_eq.lean"
**[DataTypesAsLattices/Functionality/Zcomb.lean](DomainTheory/DataTypesAsLattices/Functionality/Zcomb.lean)**

@import "Zcomb.lean"
**[DataTypesAsLattices/Functionality/arrowE.lean](DomainTheory/DataTypesAsLattices/Functionality/arrowE.lean)**

@import "arrowE.lean"
**[DataTypesAsLattices/Functionality/normalized_finite_app.lean](DomainTheory/DataTypesAsLattices/Functionality/normalized_finite_app.lean)**

@import "normalized_finite_app.lean"
**[DataTypesAsLattices/Functionality/finite_sigma_plain_app.lean](DomainTheory/DataTypesAsLattices/Functionality/finite_sigma_plain_app.lean)**

@import "finite_sigma_plain_app.lean"
**[DataTypesAsLattices/Functionality/outC.lean](DomainTheory/DataTypesAsLattices/Functionality/outC.lean)**

@import "outC.lean"
**[DataTypesAsLattices/Functionality/pairSeq_app_one.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_app_one.lean)**

@import "pairSeq_app_one.lean"
**[DataTypesAsLattices/Functionality/pairSeq_app_zero.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_app_zero.lean)**

@import "pairSeq_app_zero.lean"
**[DataTypesAsLattices/Functionality/pairSeq_inj.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_inj.lean)**

@import "pairSeq_inj.lean"
**[DataTypesAsLattices/Functionality/pairElem.lean](DomainTheory/DataTypesAsLattices/Functionality/pairElem.lean)**

@import "pairElem.lean"
**[DataTypesAsLattices/Functionality/pairSeq_isScottContinuous_right.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_isScottContinuous_right.lean)**

@import "pairSeq_isScottContinuous_right.lean"
**[DataTypesAsLattices/Functionality/inleftC.lean](DomainTheory/DataTypesAsLattices/Functionality/inleftC.lean)**

@import "inleftC.lean"
**[DataTypesAsLattices/Functionality/hZero.lean](DomainTheory/DataTypesAsLattices/Functionality/hZero.lean)**

@import "hZero.lean"
**[DataTypesAsLattices/Functionality/predSet_iterate_expTag_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/predSet_iterate_expTag_isScottContinuous.lean)**

@import "predSet_iterate_expTag_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/predSet_iterate_ofNat.lean](DomainTheory/DataTypesAsLattices/Functionality/predSet_iterate_ofNat.lean)**

@import "predSet_iterate_ofNat.lean"
**[DataTypesAsLattices/Functionality/predSet_iterate_self.lean](DomainTheory/DataTypesAsLattices/Functionality/predSet_iterate_self.lean)**

@import "predSet_iterate_self.lean"
**[DataTypesAsLattices/Functionality/seq4_body_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_body_isScottContinuous.lean)**

@import "seq4_body_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/sumE.lean](DomainTheory/DataTypesAsLattices/Functionality/sumE.lean)**

@import "sumE.lean"
**[DataTypesAsLattices/Functionality/sumMed.lean](DomainTheory/DataTypesAsLattices/Functionality/sumMed.lean)**

@import "sumMed.lean"
**[DataTypesAsLattices/Functionality/typed_apply_retract.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_apply_retract.lean)**

@import "typed_apply_retract.lean"
**[DataTypesAsLattices/Retracts/bot_isRetract.lean](DomainTheory/DataTypesAsLattices/Retracts/bot_isRetract.lean)**

@import "../Retracts/bot_isRetract.lean"
**[DataTypesAsLattices/Retracts/fstC.lean](DomainTheory/DataTypesAsLattices/Retracts/fstC.lean)**

@import "../Retracts/fstC.lean"
**[DataTypesAsLattices/Functionality/whichC.lean](DomainTheory/DataTypesAsLattices/Functionality/whichC.lean)**

@import "whichC.lean"
**[DataTypesAsLattices/Functionality/hApp.lean](DomainTheory/DataTypesAsLattices/Functionality/hApp.lean)**

@import "hApp.lean"
**[DataTypesAsLattices/Functionality/hPred.lean](DomainTheory/DataTypesAsLattices/Functionality/hPred.lean)**

@import "hPred.lean"
**[DataTypesAsLattices/Functionality/hSucc.lean](DomainTheory/DataTypesAsLattices/Functionality/hSucc.lean)**

@import "hSucc.lean"
**[DataTypesAsLattices/Retracts/plusR.lean](DomainTheory/DataTypesAsLattices/Retracts/plusR.lean)**

@import "../Retracts/plusR.lean"
**[DataTypesAsLattices/Retracts/seq4.lean](DomainTheory/DataTypesAsLattices/Retracts/seq4.lean)**

@import "../Retracts/seq4.lean"
**[DataTypesAsLattices/Functionality/seq4_app.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_app.lean)**

@import "seq4_app.lean"
**[DataTypesAsLattices/Retracts/tagInj.lean](DomainTheory/DataTypesAsLattices/Retracts/tagInj.lean)**

@import "../Retracts/tagInj.lean"
**[DataTypesAsLattices/Functionality/tagInj_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tagInj_isScottContinuous.lean)**

@import "tagInj_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/encodeExp.lean](DomainTheory/DataTypesAsLattices/Functionality/encodeExp.lean)**

@import "encodeExp.lean"
**[DataTypesAsLattices/Functionality/tagInj_one.lean](DomainTheory/DataTypesAsLattices/Functionality/tagInj_one.lean)**

@import "tagInj_one.lean"
**[DataTypesAsLattices/Functionality/tagInj_zero.lean](DomainTheory/DataTypesAsLattices/Functionality/tagInj_zero.lean)**

@import "tagInj_zero.lean"
**[DataTypesAsLattices/Retracts/plus7Body.lean](DomainTheory/DataTypesAsLattices/Retracts/plus7Body.lean)**

@import "../Retracts/plus7Body.lean"
**[DataTypesAsLattices/Retracts/plus7.lean](DomainTheory/DataTypesAsLattices/Retracts/plus7.lean)**

@import "../Retracts/plus7.lean"
**[DataTypesAsLattices/Retracts/tensor4.lean](DomainTheory/DataTypesAsLattices/Retracts/tensor4.lean)**

@import "../Retracts/tensor4.lean"
**[DataTypesAsLattices/Retracts/tensorR.lean](DomainTheory/DataTypesAsLattices/Retracts/tensorR.lean)**

@import "../Retracts/tensorR.lean"
**[DataTypesAsLattices/Retracts/treeF.lean](DomainTheory/DataTypesAsLattices/Retracts/treeF.lean)**

@import "../Retracts/treeF.lean"
**[DataTypesAsLattices/Retracts/treeR.lean](DomainTheory/DataTypesAsLattices/Retracts/treeR.lean)**

@import "../Retracts/treeR.lean"
**[DataTypesAsLattices/Retracts/updateEnv.lean](DomainTheory/DataTypesAsLattices/Retracts/updateEnv.lean)**

@import "../Retracts/updateEnv.lean"
**[DataTypesAsLattices/Functionality/updateEnv_isScottContinuous_t.lean](DomainTheory/DataTypesAsLattices/Functionality/updateEnv_isScottContinuous_t.lean)**

@import "updateEnv_isScottContinuous_t.lean"
**[DataTypesAsLattices/Functionality/updateEnvUnion.lean](DomainTheory/DataTypesAsLattices/Functionality/updateEnvUnion.lean)**

@import "updateEnvUnion.lean"
**[DataTypesAsLattices/Functionality/hLam.lean](DomainTheory/DataTypesAsLattices/Functionality/hLam.lean)**

@import "hLam.lean"
**[DataTypesAsLattices/Functionality/funOf_e_union_fresh.lean](DomainTheory/DataTypesAsLattices/Functionality/funOf_e_union_fresh.lean)**

@import "funOf_e_union_fresh.lean"
**[DataTypesAsLattices/Functionality/normalized_finite_fresh_app.lean](DomainTheory/DataTypesAsLattices/Functionality/normalized_finite_fresh_app.lean)**

@import "normalized_finite_fresh_app.lean"
**[DataTypesAsLattices/Functionality/finite_sigma_union_app.lean](DomainTheory/DataTypesAsLattices/Functionality/finite_sigma_union_app.lean)**

@import "finite_sigma_union_app.lean"
**[DataTypesAsLattices/Functionality/funOf_top.lean](DomainTheory/DataTypesAsLattices/Functionality/funOf_top.lean)**

@import "funOf_top.lean"
**[DataTypesAsLattices/Functionality/plus7_comp_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_comp_isScottContinuous.lean)**

@import "plus7_comp_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/plus7_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_map_isScottContinuous.lean)**

@import "plus7_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/plus7_app.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app.lean)**

@import "plus7_app.lean"
**[DataTypesAsLattices/Functionality/plus7_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_isRetract.lean)**

@import "plus7_isRetract.lean"
**[DataTypesAsLattices/Functionality/plusR_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_map_isScottContinuous.lean)**

@import "plusR_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/plusR_app.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_app.lean)**

@import "plusR_app.lean"
**[DataTypesAsLattices/Functionality/plusR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_isRetract.lean)**

@import "plusR_isRetract.lean"
**[DataTypesAsLattices/Functionality/plusR_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_right_isScottContinuous.lean)**

@import "plusR_right_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/tensorR_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_right_isScottContinuous.lean)**

@import "tensorR_right_isScottContinuous.lean"
**[DataTypesAsLattices/Retracts/expF.lean](DomainTheory/DataTypesAsLattices/Retracts/expF.lean)**

@import "../Retracts/expF.lean"
**[DataTypesAsLattices/Retracts/expR.lean](DomainTheory/DataTypesAsLattices/Retracts/expR.lean)**

@import "../Retracts/expR.lean"
**[DataTypesAsLattices/Retracts/iterates_areRetracts.lean](DomainTheory/DataTypesAsLattices/Retracts/iterates_areRetracts.lean)**

@import "../Retracts/iterates_areRetracts.lean"
**[DataTypesAsLattices/Retracts/iterateBot_isStrict.lean](DomainTheory/DataTypesAsLattices/Retracts/iterateBot_isStrict.lean)**

@import "../Retracts/iterateBot_isStrict.lean"
**[DataTypesAsLattices/Retracts/iterateBot_retractLe.lean](DomainTheory/DataTypesAsLattices/Retracts/iterateBot_retractLe.lean)**

@import "../Retracts/iterateBot_retractLe.lean"
**[DataTypesAsLattices/Retracts/fixedToInverseLimit.lean](DomainTheory/DataTypesAsLattices/Retracts/fixedToInverseLimit.lean)**

@import "../Retracts/fixedToInverseLimit.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_project_earlier.lean](DomainTheory/DataTypesAsLattices/Retracts/inverseLimit_project_earlier.lean)**

@import "../Retracts/inverseLimit_project_earlier.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_project_later.lean](DomainTheory/DataTypesAsLattices/Retracts/inverseLimit_project_later.lean)**

@import "../Retracts/inverseLimit_project_later.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_project_iUnion.lean](DomainTheory/DataTypesAsLattices/Retracts/inverseLimit_project_iUnion.lean)**

@import "../Retracts/inverseLimit_project_iUnion.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_iUnion_typed.lean](DomainTheory/DataTypesAsLattices/Retracts/inverseLimit_iUnion_typed.lean)**

@import "../Retracts/inverseLimit_iUnion_typed.lean"
**[DataTypesAsLattices/Retracts/inverseLimitToFixed.lean](DomainTheory/DataTypesAsLattices/Retracts/inverseLimitToFixed.lean)**

@import "../Retracts/inverseLimitToFixed.lean"
**[DataTypesAsLattices/Retracts/lambF.lean](DomainTheory/DataTypesAsLattices/Retracts/lambF.lean)**

@import "../Retracts/lambF.lean"
**[DataTypesAsLattices/Retracts/lambR.lean](DomainTheory/DataTypesAsLattices/Retracts/lambR.lean)**

@import "../Retracts/lambR.lean"
**[DataTypesAsLattices/Functionality/Hinterp.lean](DomainTheory/DataTypesAsLattices/Functionality/Hinterp.lean)**

@import "Hinterp.lean"
**[DataTypesAsLattices/Functionality/hCond.lean](DomainTheory/DataTypesAsLattices/Functionality/hCond.lean)**

@import "hCond.lean"
**[DataTypesAsLattices/Functionality/Hstep.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep.lean)**

@import "Hstep.lean"
**[DataTypesAsLattices/Retracts/envR.lean](DomainTheory/DataTypesAsLattices/Retracts/envR.lean)**

@import "../Retracts/envR.lean"
**[DataTypesAsLattices/Functionality/HF.lean](DomainTheory/DataTypesAsLattices/Functionality/HF.lean)**

@import "HF.lean"
**[DataTypesAsLattices/Functionality/Hfun.lean](DomainTheory/DataTypesAsLattices/Functionality/Hfun.lean)**

@import "Hfun.lean"
**[DataTypesAsLattices/Functionality/envR_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/envR_map_isScottContinuous.lean)**

@import "envR_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/envR_app.lean](DomainTheory/DataTypesAsLattices/Functionality/envR_app.lean)**

@import "envR_app.lean"
**[DataTypesAsLattices/Functionality/lambF_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/lambF_isScottContinuous.lean)**

@import "lambF_isScottContinuous.lean"
**[DataTypesAsLattices/Retracts/retract_isGraph.lean](DomainTheory/DataTypesAsLattices/Retracts/retract_isGraph.lean)**

@import "../Retracts/retract_isGraph.lean"
**[DataTypesAsLattices/Retracts/iUnion_retract_isGraph.lean](DomainTheory/DataTypesAsLattices/Retracts/iUnion_retract_isGraph.lean)**

@import "../Retracts/iUnion_retract_isGraph.lean"
**[DataTypesAsLattices/Functionality/pairSeq_isScottContinuous_left.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_isScottContinuous_left.lean)**

@import "pairSeq_isScottContinuous_left.lean"
**[DataTypesAsLattices/Functionality/tensorR_diag_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_diag_isScottContinuous.lean)**

@import "tensorR_diag_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/tensorR_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_map_isScottContinuous.lean)**

@import "tensorR_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/tensorR_app.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_app.lean)**

@import "tensorR_app.lean"
**[DataTypesAsLattices/Functionality/tensorR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_isRetract.lean)**

@import "tensorR_isRetract.lean"
**[DataTypesAsLattices/Functionality/seq4_comp_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_comp_isScottContinuous.lean)**

@import "seq4_comp_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/tensor4_diag_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tensor4_diag_isScottContinuous.lean)**

@import "tensor4_diag_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/expF_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/expF_isScottContinuous.lean)**

@import "expF_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/tensor4_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tensor4_map_isScottContinuous.lean)**

@import "tensor4_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/tensor4_app.lean](DomainTheory/DataTypesAsLattices/Functionality/tensor4_app.lean)**

@import "tensor4_app.lean"
**[DataTypesAsLattices/Functionality/tensor4_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/tensor4_isRetract.lean)**

@import "tensor4_isRetract.lean"
**[DataTypesAsLattices/Graph/mu_law.lean](DomainTheory/DataTypesAsLattices/Graph/mu_law.lean)**

@import "../Graph/mu_law.lean"
**[DataTypesAsLattices/Retracts/funOf_fix_idem.lean](DomainTheory/DataTypesAsLattices/Retracts/funOf_fix_idem.lean)**

@import "../Retracts/funOf_fix_idem.lean"
**[DataTypesAsLattices/Retracts/theorem_4_6.lean](DomainTheory/DataTypesAsLattices/Retracts/theorem_4_6.lean)**

@import "../Retracts/theorem_4_6.lean"
**[DataTypesAsLattices/Functionality/expR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/expR_isRetract.lean)**

@import "expR_isRetract.lean"
**[DataTypesAsLattices/Retracts/theorem_4_3_more.lean](DomainTheory/DataTypesAsLattices/Retracts/theorem_4_3_more.lean)**

@import "../Retracts/theorem_4_3_more.lean"
**[DataTypesAsLattices/Retracts/typed_more.lean](DomainTheory/DataTypesAsLattices/Retracts/typed_more.lean)**

@import "../Retracts/typed_more.lean"
**[DataTypesAsLattices/Retracts/arrowR_more.lean](DomainTheory/DataTypesAsLattices/Retracts/arrowR_more.lean)**

@import "../Retracts/arrowR_more.lean"
**[DataTypesAsLattices/Functionality/lambR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/lambR_isRetract.lean)**

@import "lambR_isRetract.lean"
**[DataTypesAsLattices/Functionality/envR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/envR_isRetract.lean)**

@import "envR_isRetract.lean"
**[DataTypesAsLattices/Functionality/Hcomb.lean](DomainTheory/DataTypesAsLattices/Functionality/Hcomb.lean)**

@import "Hcomb.lean"
**[DataTypesAsLattices/Closures/theorem_5_5_more.lean](DomainTheory/DataTypesAsLattices/Closures/theorem_5_5_more.lean)**

@import "../Closures/theorem_5_5_more.lean"
**[DataTypesAsLattices/Closures/eq_5_19.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_19.lean)**

@import "../Closures/eq_5_19.lean"
**[DataTypesAsLattices/Closures/Vcomb_more.lean](DomainTheory/DataTypesAsLattices/Closures/Vcomb_more.lean)**

@import "../Closures/Vcomb_more.lean"
**[DataTypesAsLattices/Closures/eq_5_21.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_21.lean)**

@import "../Closures/eq_5_21.lean"
**[DataTypesAsLattices/Closures/Icomb_subset_Vcomb.lean](DomainTheory/DataTypesAsLattices/Closures/Icomb_subset_Vcomb.lean)**

@import "../Closures/Icomb_subset_Vcomb.lean"
**[DataTypesAsLattices/Closures/theorem_5_5_universe.lean](DomainTheory/DataTypesAsLattices/Closures/theorem_5_5_universe.lean)**

@import "../Closures/theorem_5_5_universe.lean"
**[DataTypesAsLattices/Closures/eq_5_22.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_22.lean)**

@import "../Closures/eq_5_22.lean"
**[DataTypesAsLattices/Closures/eq_5_23.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_23.lean)**

@import "../Closures/eq_5_23.lean"
**[DataTypesAsLattices/Retracts/theorem_4_3.lean](DomainTheory/DataTypesAsLattices/Retracts/theorem_4_3.lean)**

@import "../Retracts/theorem_4_3.lean"
**[DataTypesAsLattices/Closures/theorem_5_3.lean](DomainTheory/DataTypesAsLattices/Closures/theorem_5_3.lean)**

@import "../Closures/theorem_5_3.lean"
**[DataTypesAsLattices/Closures/eq_5_24.lean](DomainTheory/DataTypesAsLattices/Closures/eq_5_24.lean)**

@import "../Closures/eq_5_24.lean"
**[DataTypesAsLattices/Closures/theorem_5_6.lean](DomainTheory/DataTypesAsLattices/Closures/theorem_5_6.lean)**

@import "../Closures/theorem_5_6.lean"
**[DataTypesAsLattices/Functionality/Ea.lean](DomainTheory/DataTypesAsLattices/Functionality/Ea.lean)**

@import "Ea.lean"
**[DataTypesAsLattices/Functionality/Htyped.lean](DomainTheory/DataTypesAsLattices/Functionality/Htyped.lean)**

@import "Htyped.lean"
**[DataTypesAsLattices/Functionality/Icomb_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Icomb_isGraph.lean)**

@import "Icomb_isGraph.lean"
**[DataTypesAsLattices/Functionality/Kcomb_app.lean](DomainTheory/DataTypesAsLattices/Functionality/Kcomb_app.lean)**

@import "Kcomb_app.lean"
**[DataTypesAsLattices/Functionality/Kcomb_app2.lean](DomainTheory/DataTypesAsLattices/Functionality/Kcomb_app2.lean)**

@import "Kcomb_app2.lean"
**[DataTypesAsLattices/Functionality/Kcomb_app_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Kcomb_app_isGraph.lean)**

@import "Kcomb_app_isGraph.lean"
**[DataTypesAsLattices/Functionality/Kcomb_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Kcomb_isGraph.lean)**

@import "Kcomb_isGraph.lean"
**[DataTypesAsLattices/Functionality/Nk.lean](DomainTheory/DataTypesAsLattices/Functionality/Nk.lean)**

@import "Nk.lean"
**[DataTypesAsLattices/Functionality/Nrel.lean](DomainTheory/DataTypesAsLattices/Functionality/Nrel.lean)**

@import "Nrel.lean"
**[DataTypesAsLattices/Functionality/Scomb_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_map_isScottContinuous.lean)**

@import "Scomb_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/Scomb_app.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_app.lean)**

@import "Scomb_app.lean"
**[DataTypesAsLattices/Functionality/Scomb_mid_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_mid_isScottContinuous.lean)**

@import "Scomb_mid_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/Scomb_app2.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_app2.lean)**

@import "Scomb_app2.lean"
**[DataTypesAsLattices/Functionality/Scomb_inner_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_inner_isScottContinuous.lean)**

@import "Scomb_inner_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/Scomb_app2_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_app2_isGraph.lean)**

@import "Scomb_app2_isGraph.lean"
**[DataTypesAsLattices/Functionality/Scomb_app3.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_app3.lean)**

@import "Scomb_app3.lean"
**[DataTypesAsLattices/Functionality/Scomb_app_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_app_isGraph.lean)**

@import "Scomb_app_isGraph.lean"
**[DataTypesAsLattices/Functionality/Scomb_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_isGraph.lean)**

@import "Scomb_isGraph.lean"
**[DataTypesAsLattices/Functionality/comp_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/comp_isGraph.lean)**

@import "comp_isGraph.lean"
**[DataTypesAsLattices/Functionality/curryC_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/curryC_isScottContinuous.lean)**

@import "curryC_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/curryC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/curryC_app.lean)**

@import "curryC_app.lean"
**[DataTypesAsLattices/Functionality/curry_mid_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/curry_mid_isScottContinuous.lean)**

@import "curry_mid_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/diagC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/diagC_app.lean)**

@import "diagC_app.lean"
**[DataTypesAsLattices/Functionality/emptyE.lean](DomainTheory/DataTypesAsLattices/Functionality/emptyE.lean)**

@import "emptyE.lean"
**[DataTypesAsLattices/Functionality/eq_4_44.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_44.lean)**

@import "eq_4_44.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl0.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl0.lean)**

@import "plus7_typed_inl0.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl1.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl1.lean)**

@import "plus7_typed_inl1.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl2.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl2.lean)**

@import "plus7_typed_inl2.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl3.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl3.lean)**

@import "plus7_typed_inl3.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl4.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl4.lean)**

@import "plus7_typed_inl4.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl5.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl5.lean)**

@import "plus7_typed_inl5.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl6.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl6.lean)**

@import "plus7_typed_inl6.lean"
**[DataTypesAsLattices/Functionality/typed_bot_botElem.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_bot_botElem.lean)**

@import "typed_bot_botElem.lean"
**[DataTypesAsLattices/Functionality/typed_ofNat_intR.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_ofNat_intR.lean)**

@import "typed_ofNat_intR.lean"
**[DataTypesAsLattices/Functionality/typed_pairSeq_tensorR.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_pairSeq_tensorR.lean)**

@import "typed_pairSeq_tensorR.lean"
**[DataTypesAsLattices/Functionality/encodeExp_typed.lean](DomainTheory/DataTypesAsLattices/Functionality/encodeExp_typed.lean)**

@import "encodeExp_typed.lean"
**[DataTypesAsLattices/Functionality/eq_4_12.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_12.lean)**

@import "eq_4_12.lean"
**[DataTypesAsLattices/Functionality/eq_4_13.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_13.lean)**

@import "eq_4_13.lean"
**[DataTypesAsLattices/Functionality/eq_4_17.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_17.lean)**

@import "eq_4_17.lean"
**[DataTypesAsLattices/Functionality/eq_4_18.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_18.lean)**

@import "eq_4_18.lean"
**[DataTypesAsLattices/Functionality/eq_4_19.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_19.lean)**

@import "eq_4_19.lean"
**[DataTypesAsLattices/Functionality/eq_4_20.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_20.lean)**

@import "eq_4_20.lean"
**[DataTypesAsLattices/Functionality/eq_4_21.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_21.lean)**

@import "eq_4_21.lean"
**[DataTypesAsLattices/Functionality/evalC_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/evalC_isScottContinuous.lean)**

@import "evalC_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/evalC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/evalC_app.lean)**

@import "evalC_app.lean"
**[DataTypesAsLattices/Functionality/eq_4_24.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_24.lean)**

@import "eq_4_24.lean"
**[DataTypesAsLattices/Functionality/eq_4_25.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_25.lean)**

@import "eq_4_25.lean"
**[DataTypesAsLattices/Functionality/eq_4_32.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_32.lean)**

@import "eq_4_32.lean"
**[DataTypesAsLattices/Functionality/inrightC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/inrightC_app.lean)**

@import "inrightC_app.lean"
**[DataTypesAsLattices/Functionality/eq_4_33.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_33.lean)**

@import "eq_4_33.lean"
**[DataTypesAsLattices/Functionality/outleftC.lean](DomainTheory/DataTypesAsLattices/Functionality/outleftC.lean)**

@import "outleftC.lean"
**[DataTypesAsLattices/Functionality/eq_4_34.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_34.lean)**

@import "eq_4_34.lean"
**[DataTypesAsLattices/Functionality/outrightC.lean](DomainTheory/DataTypesAsLattices/Functionality/outrightC.lean)**

@import "outrightC.lean"
**[DataTypesAsLattices/Functionality/eq_4_35.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_35.lean)**

@import "eq_4_35.lean"
**[DataTypesAsLattices/Functionality/funOf_condSet.lean](DomainTheory/DataTypesAsLattices/Functionality/funOf_condSet.lean)**

@import "funOf_condSet.lean"
**[DataTypesAsLattices/Functionality/funOf_dcondSet.lean](DomainTheory/DataTypesAsLattices/Functionality/funOf_dcondSet.lean)**

@import "funOf_dcondSet.lean"
**[DataTypesAsLattices/Functionality/plusR_fst.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_fst.lean)**

@import "plusR_fst.lean"
**[DataTypesAsLattices/Functionality/eq_4_36.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_36.lean)**

@import "eq_4_36.lean"
**[DataTypesAsLattices/Functionality/eq_4_37.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_37.lean)**

@import "eq_4_37.lean"
**[DataTypesAsLattices/Functionality/eq_4_39.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_39.lean)**

@import "eq_4_39.lean"
**[DataTypesAsLattices/Functionality/eq_4_45.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_45.lean)**

@import "eq_4_45.lean"
**[DataTypesAsLattices/Functionality/eq_7_19.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_7_19.lean)**

@import "eq_7_19.lean"
**[DataTypesAsLattices/Functionality/eraseTag.lean](DomainTheory/DataTypesAsLattices/Functionality/eraseTag.lean)**

@import "eraseTag.lean"
**[DataTypesAsLattices/Functionality/eta2_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/eta2_map_isScottContinuous.lean)**

@import "eta2_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/eta2_app.lean](DomainTheory/DataTypesAsLattices/Functionality/eta2_app.lean)**

@import "eta2_app.lean"
**[DataTypesAsLattices/Functionality/graph_funOf_ext.lean](DomainTheory/DataTypesAsLattices/Functionality/graph_funOf_ext.lean)**

@import "graph_funOf_ext.lean"
**[DataTypesAsLattices/Functionality/iterateE.lean](DomainTheory/DataTypesAsLattices/Functionality/iterateE.lean)**

@import "iterateE.lean"
**[DataTypesAsLattices/Functionality/kerE.lean](DomainTheory/DataTypesAsLattices/Functionality/kerE.lean)**

@import "kerE.lean"
**[DataTypesAsLattices/Functionality/pairMed.lean](DomainTheory/DataTypesAsLattices/Functionality/pairMed.lean)**

@import "pairMed.lean"
**[DataTypesAsLattices/Functionality/plotkinGood.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkinGood.lean)**

@import "plotkinGood.lean"
**[DataTypesAsLattices/Functionality/plotkinRel.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkinRel.lean)**

@import "plotkinRel.lean"
**[DataTypesAsLattices/Functionality/plotkinE.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkinE.lean)**

@import "plotkinE.lean"
**[DataTypesAsLattices/Functionality/plotkin_finite_separation.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkin_finite_separation.lean)**

@import "plotkin_finite_separation.lean"
**[DataTypesAsLattices/Functionality/plotkin_function_related.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkin_function_related.lean)**

@import "plotkin_function_related.lean"
**[DataTypesAsLattices/Functionality/plusR_isStrict.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_isStrict.lean)**

@import "plusR_isStrict.lean"
**[DataTypesAsLattices/Functionality/plusR_typed_bot.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_typed_bot.lean)**

@import "plusR_typed_bot.lean"
**[DataTypesAsLattices/Functionality/plusR_typed_inl.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_typed_inl.lean)**

@import "plusR_typed_inl.lean"
**[DataTypesAsLattices/Functionality/plusR_typed_inr.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_typed_inr.lean)**

@import "plusR_typed_inr.lean"
**[DataTypesAsLattices/Functionality/plusR_typed_top.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_typed_top.lean)**

@import "plusR_typed_top.lean"
**[DataTypesAsLattices/Functionality/plusR_typed_iff.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_typed_iff.lean)**

@import "plusR_typed_iff.lean"
**[DataTypesAsLattices/Functionality/prodE.lean](DomainTheory/DataTypesAsLattices/Functionality/prodE.lean)**

@import "prodE.lean"
**[DataTypesAsLattices/Functionality/singletonE.lean](DomainTheory/DataTypesAsLattices/Functionality/singletonE.lean)**

@import "singletonE.lean"
**[DataTypesAsLattices/Functionality/singletonE_mem.lean](DomainTheory/DataTypesAsLattices/Functionality/singletonE_mem.lean)**

@import "singletonE_mem.lean"
**[DataTypesAsLattices/Functionality/typed_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_isGraph.lean)**

@import "typed_isGraph.lean"
**[DataTypesAsLattices/Functionality/theorem_4_4_med.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_4_4_med.lean)**

@import "theorem_4_4_med.lean"
**[DataTypesAsLattices/Functionality/theorem_4_4_med_unique.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_4_4_med_unique.lean)**

@import "theorem_4_4_med_unique.lean"
**[DataTypesAsLattices/Functionality/theorem_4_4_typed.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_4_4_typed.lean)**

@import "theorem_4_4_typed.lean"
**[DataTypesAsLattices/Functionality/theorem_4_5_sum.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_4_5_sum.lean)**

@import "theorem_4_5_sum.lean"
**[DataTypesAsLattices/Functionality/theorem_7_1.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_1.lean)**

@import "theorem_7_1.lean"
**[DataTypesAsLattices/Functionality/theorem_7_2.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_2.lean)**

@import "theorem_7_2.lean"
**[DataTypesAsLattices/Functionality/theorem_7_3.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_3.lean)**

@import "theorem_7_3.lean"
**[DataTypesAsLattices/Functionality/theorem_7_4.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_4.lean)**

@import "theorem_7_4.lean"
**[DataTypesAsLattices/Retracts/theorem_4_4.lean](DomainTheory/DataTypesAsLattices/Retracts/theorem_4_4.lean)**

@import "../Retracts/theorem_4_4.lean"
**[DataTypesAsLattices/Retracts/theorem_4_5.lean](DomainTheory/DataTypesAsLattices/Retracts/theorem_4_5.lean)**

@import "../Retracts/theorem_4_5.lean"
