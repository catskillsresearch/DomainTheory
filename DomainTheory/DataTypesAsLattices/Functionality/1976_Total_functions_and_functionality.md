# Total functions and functionality

**Historical note.** Functionality had long been studied in combinatory logic. Hindley, Lercher, and Seldin (1972) is the introduction Scott used. This section is his reading of that theory in $\mathbf{P}\omega$. The connection with the functional interpretation of intuitionistic logic goes back to Curry and Kleene, and Theorem 7.3 is the standard result of that interpretation. Theorem 7.4, that the obvious typing characterizes the iterators, is due to Gordon Plotkin.

**Dependencies.** Inside Functionality, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Functionality.mermaid"

@import "1976_Total_functions_and_functionality.english" {code_block=false}

- [Definition (equivalence)](1976_Definition_equivalence.md)
- [Theorem 7.1](1976_Theorem_7_1.md)
- [Theorem 7.2](1976_Theorem_7_2.md)
- [Theorem 7.3](1976_Theorem_7_3.md)
- [Theorem 7.4](1976_Theorem_7_4.md)


**[DataTypesAsLattices/Functionality/expPayload.lean](expPayload.lean)**

@import "expPayload.lean"
**[DataTypesAsLattices/Functionality/graph_funOf_ext.lean](graph_funOf_ext.lean)**

@import "graph_funOf_ext.lean"
**[DataTypesAsLattices/Functionality/typed_apply_retract.lean](typed_apply_retract.lean)**

@import "typed_apply_retract.lean"
**[DataTypesAsLattices/Functionality/funOf_top.lean](funOf_top.lean)**

@import "funOf_top.lean"
**[DataTypesAsLattices/Graph/mu_law.lean](../Graph/mu_law.lean)**

@import "../Graph/mu_law.lean"
**[DataTypesAsLattices/Retracts/bot_isRetract.lean](../Retracts/bot_isRetract.lean)**

@import "../Retracts/bot_isRetract.lean"
**[DataTypesAsLattices/Retracts/theorem_4_4.lean](../Retracts/theorem_4_4.lean)**

@import "../Retracts/theorem_4_4.lean"
**[DataTypesAsLattices/Retracts/theorem_4_5.lean](../Retracts/theorem_4_5.lean)**

@import "../Retracts/theorem_4_5.lean"
**[DataTypesAsLattices/Retracts/retract_isGraph.lean](../Retracts/retract_isGraph.lean)**

@import "../Retracts/retract_isGraph.lean"
**[DataTypesAsLattices/Closures/theorem_5_5_more.lean](../Closures/theorem_5_5_more.lean)**

@import "../Closures/theorem_5_5_more.lean"
**[DataTypesAsLattices/Retracts/updateEnv.lean](../Retracts/updateEnv.lean)**

@import "../Retracts/updateEnv.lean"
**[DataTypesAsLattices/Functionality/sigmaJ.lean](sigmaJ.lean)**

@import "sigmaJ.lean"
**[DataTypesAsLattices/Functionality/eta2_map_isScottContinuous.lean](eta2_map_isScottContinuous.lean)**

@import "eta2_map_isScottContinuous.lean"
**[DataTypesAsLattices/Retracts/iterates_areRetracts.lean](../Retracts/iterates_areRetracts.lean)**

@import "../Retracts/iterates_areRetracts.lean"
**[DataTypesAsLattices/Closures/eq_5_19.lean](../Closures/eq_5_19.lean)**

@import "../Closures/eq_5_19.lean"
**[DataTypesAsLattices/Functionality/pairSeq_app_one.lean](pairSeq_app_one.lean)**

@import "pairSeq_app_one.lean"
**[DataTypesAsLattices/Functionality/typed_ofNat_intR.lean](typed_ofNat_intR.lean)**

@import "typed_ofNat_intR.lean"
**[DataTypesAsLattices/Retracts/iUnion_retract_isGraph.lean](../Retracts/iUnion_retract_isGraph.lean)**

@import "../Retracts/iUnion_retract_isGraph.lean"
**[DataTypesAsLattices/Functionality/eta2_app.lean](eta2_app.lean)**

@import "eta2_app.lean"
**[DataTypesAsLattices/Functionality/comp_isGraph.lean](comp_isGraph.lean)**

@import "comp_isGraph.lean"
**[DataTypesAsLattices/Retracts/iterateBot_isStrict.lean](../Retracts/iterateBot_isStrict.lean)**

@import "../Retracts/iterateBot_isStrict.lean"
**[DataTypesAsLattices/Functionality/pairSeq_isScottContinuous_left.lean](pairSeq_isScottContinuous_left.lean)**

@import "pairSeq_isScottContinuous_left.lean"
**[DataTypesAsLattices/Functionality/curry_mid_isScottContinuous.lean](curry_mid_isScottContinuous.lean)**

@import "curry_mid_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/Vcomb_more.lean](../Closures/Vcomb_more.lean)**

@import "../Closures/Vcomb_more.lean"
**[DataTypesAsLattices/Functionality/funOf_e_union_fresh.lean](funOf_e_union_fresh.lean)**

@import "funOf_e_union_fresh.lean"
**[DataTypesAsLattices/Retracts/tensorR.lean](../Retracts/tensorR.lean)**

@import "../Retracts/tensorR.lean"
**[DataTypesAsLattices/Functionality/hVar.lean](hVar.lean)**

@import "hVar.lean"
**[DataTypesAsLattices/Retracts/tagInj.lean](../Retracts/tagInj.lean)**

@import "../Retracts/tagInj.lean"
**[DataTypesAsLattices/Functionality/tagInj_one.lean](tagInj_one.lean)**

@import "tagInj_one.lean"
**[DataTypesAsLattices/Retracts/plus7Body.lean](../Retracts/plus7Body.lean)**

@import "../Retracts/plus7Body.lean"
**[DataTypesAsLattices/Retracts/plus7.lean](../Retracts/plus7.lean)**

@import "../Retracts/plus7.lean"
**[DataTypesAsLattices/Retracts/iterateBot_retractLe.lean](../Retracts/iterateBot_retractLe.lean)**

@import "../Retracts/iterateBot_retractLe.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_project_later.lean](../Retracts/inverseLimit_project_later.lean)**

@import "../Retracts/inverseLimit_project_later.lean"
**[DataTypesAsLattices/Retracts/fixedToInverseLimit.lean](../Retracts/fixedToInverseLimit.lean)**

@import "../Retracts/fixedToInverseLimit.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_project_earlier.lean](../Retracts/inverseLimit_project_earlier.lean)**

@import "../Retracts/inverseLimit_project_earlier.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_project_iUnion.lean](../Retracts/inverseLimit_project_iUnion.lean)**

@import "../Retracts/inverseLimit_project_iUnion.lean"
**[DataTypesAsLattices/Functionality/normalized_finite_app.lean](normalized_finite_app.lean)**

@import "normalized_finite_app.lean"
**[DataTypesAsLattices/Functionality/Icomb_isGraph.lean](Icomb_isGraph.lean)**

@import "Icomb_isGraph.lean"
**[DataTypesAsLattices/Functionality/outC.lean](outC.lean)**

@import "outC.lean"
**[DataTypesAsLattices/Functionality/expTag.lean](expTag.lean)**

@import "expTag.lean"
**[DataTypesAsLattices/Functionality/predSet_iterate_expTag_isScottContinuous.lean](predSet_iterate_expTag_isScottContinuous.lean)**

@import "predSet_iterate_expTag_isScottContinuous.lean"
**[DataTypesAsLattices/Closures/eq_5_21.lean](../Closures/eq_5_21.lean)**

@import "../Closures/eq_5_21.lean"
**[DataTypesAsLattices/Closures/Icomb_subset_Vcomb.lean](../Closures/Icomb_subset_Vcomb.lean)**

@import "../Closures/Icomb_subset_Vcomb.lean"
**[DataTypesAsLattices/Closures/theorem_5_5_universe.lean](../Closures/theorem_5_5_universe.lean)**

@import "../Closures/theorem_5_5_universe.lean"
**[DataTypesAsLattices/Closures/eq_5_23.lean](../Closures/eq_5_23.lean)**

@import "../Closures/eq_5_23.lean"
**[DataTypesAsLattices/Closures/eq_5_22.lean](../Closures/eq_5_22.lean)**

@import "../Closures/eq_5_22.lean"
**[DataTypesAsLattices/Functionality/Scomb_mid_isScottContinuous.lean](Scomb_mid_isScottContinuous.lean)**

@import "Scomb_mid_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/predSet_iterate_ofNat.lean](predSet_iterate_ofNat.lean)**

@import "predSet_iterate_ofNat.lean"
**[DataTypesAsLattices/Retracts/seq4.lean](../Retracts/seq4.lean)**

@import "../Retracts/seq4.lean"
**[DataTypesAsLattices/Retracts/tensor4.lean](../Retracts/tensor4.lean)**

@import "../Retracts/tensor4.lean"
**[DataTypesAsLattices/Functionality/typed_bot_botElem.lean](typed_bot_botElem.lean)**

@import "typed_bot_botElem.lean"
**[DataTypesAsLattices/Functionality/pairSeq_app_zero.lean](pairSeq_app_zero.lean)**

@import "pairSeq_app_zero.lean"
**[DataTypesAsLattices/Functionality/pairSeq_inj.lean](pairSeq_inj.lean)**

@import "pairSeq_inj.lean"
**[DataTypesAsLattices/Functionality/pairElem.lean](pairElem.lean)**

@import "pairElem.lean"
**[DataTypesAsLattices/Functionality/predSet_iterate_self.lean](predSet_iterate_self.lean)**

@import "predSet_iterate_self.lean"
**[DataTypesAsLattices/Retracts/expF.lean](../Retracts/expF.lean)**

@import "../Retracts/expF.lean"
**[DataTypesAsLattices/Retracts/expR.lean](../Retracts/expR.lean)**

@import "../Retracts/expR.lean"
**[DataTypesAsLattices/Functionality/inrightC.lean](inrightC.lean)**

@import "inrightC.lean"
**[DataTypesAsLattices/Functionality/Scomb_map_isScottContinuous.lean](Scomb_map_isScottContinuous.lean)**

@import "Scomb_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/Scomb_app.lean](Scomb_app.lean)**

@import "Scomb_app.lean"
**[DataTypesAsLattices/Functionality/Scomb_app2.lean](Scomb_app2.lean)**

@import "Scomb_app2.lean"
**[DataTypesAsLattices/Functionality/Scomb_isGraph.lean](Scomb_isGraph.lean)**

@import "Scomb_isGraph.lean"
**[DataTypesAsLattices/Functionality/Scomb_app_isGraph.lean](Scomb_app_isGraph.lean)**

@import "Scomb_app_isGraph.lean"
**[DataTypesAsLattices/Functionality/pairSeq_isScottContinuous_right.lean](pairSeq_isScottContinuous_right.lean)**

@import "pairSeq_isScottContinuous_right.lean"
**[DataTypesAsLattices/Functionality/inleftC.lean](inleftC.lean)**

@import "inleftC.lean"
**[DataTypesAsLattices/Functionality/tensorR_right_isScottContinuous.lean](tensorR_right_isScottContinuous.lean)**

@import "tensorR_right_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/inrightC_app.lean](inrightC_app.lean)**

@import "inrightC_app.lean"
**[DataTypesAsLattices/Functionality/tagInj_isScottContinuous.lean](tagInj_isScottContinuous.lean)**

@import "tagInj_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/Kcomb_app.lean](Kcomb_app.lean)**

@import "Kcomb_app.lean"
**[DataTypesAsLattices/Functionality/Kcomb_app2.lean](Kcomb_app2.lean)**

@import "Kcomb_app2.lean"
**[DataTypesAsLattices/Functionality/Kcomb_app_isGraph.lean](Kcomb_app_isGraph.lean)**

@import "Kcomb_app_isGraph.lean"
**[DataTypesAsLattices/Functionality/Kcomb_isGraph.lean](Kcomb_isGraph.lean)**

@import "Kcomb_isGraph.lean"
**[DataTypesAsLattices/Functionality/tagInj_zero.lean](tagInj_zero.lean)**

@import "tagInj_zero.lean"
**[DataTypesAsLattices/Functionality/updateEnv_isScottContinuous_t.lean](updateEnv_isScottContinuous_t.lean)**

@import "updateEnv_isScottContinuous_t.lean"
**[DataTypesAsLattices/Functionality/updateEnvUnion.lean](updateEnvUnion.lean)**

@import "updateEnvUnion.lean"
**[DataTypesAsLattices/Functionality/curryC_isScottContinuous.lean](curryC_isScottContinuous.lean)**

@import "curryC_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/curryC_app.lean](curryC_app.lean)**

@import "curryC_app.lean"
**[DataTypesAsLattices/Functionality/pairMed.lean](pairMed.lean)**

@import "pairMed.lean"
**[DataTypesAsLattices/Functionality/hZero.lean](hZero.lean)**

@import "hZero.lean"
**[DataTypesAsLattices/Functionality/funOf_condSet.lean](funOf_condSet.lean)**

@import "funOf_condSet.lean"
**[DataTypesAsLattices/Functionality/funOf_dcondSet.lean](funOf_dcondSet.lean)**

@import "funOf_dcondSet.lean"
**[DataTypesAsLattices/Retracts/funOf_fix_idem.lean](../Retracts/funOf_fix_idem.lean)**

@import "../Retracts/funOf_fix_idem.lean"
**[DataTypesAsLattices/Retracts/fstC.lean](../Retracts/fstC.lean)**

@import "../Retracts/fstC.lean"
**[DataTypesAsLattices/Functionality/whichC.lean](whichC.lean)**

@import "whichC.lean"
**[DataTypesAsLattices/Functionality/RestrictedEquiv.lean](RestrictedEquiv.lean)**

@import "RestrictedEquiv.lean"
**[DataTypesAsLattices/Functionality/sumE.lean](sumE.lean)**

@import "sumE.lean"
**[DataTypesAsLattices/Functionality/kerE.lean](kerE.lean)**

@import "kerE.lean"
**[DataTypesAsLattices/Functionality/mem.lean](mem.lean)**

@import "mem.lean"
**[DataTypesAsLattices/Functionality/emptyE.lean](emptyE.lean)**

@import "emptyE.lean"
**[DataTypesAsLattices/Functionality/Nk.lean](Nk.lean)**

@import "Nk.lean"
**[DataTypesAsLattices/Functionality/Nrel.lean](Nrel.lean)**

@import "Nrel.lean"
**[DataTypesAsLattices/Functionality/Ea.lean](Ea.lean)**

@import "Ea.lean"
**[DataTypesAsLattices/Functionality/arrowE.lean](arrowE.lean)**

@import "arrowE.lean"
**[DataTypesAsLattices/Functionality/prodE.lean](prodE.lean)**

@import "prodE.lean"
**[DataTypesAsLattices/Functionality/singletonE.lean](singletonE.lean)**

@import "singletonE.lean"
**[DataTypesAsLattices/Functionality/singletonE_mem.lean](singletonE_mem.lean)**

@import "singletonE_mem.lean"
**[DataTypesAsLattices/Retracts/plusR.lean](../Retracts/plusR.lean)**

@import "../Retracts/plusR.lean"
**[DataTypesAsLattices/Functionality/plusR_right_isScottContinuous.lean](plusR_right_isScottContinuous.lean)**

@import "plusR_right_isScottContinuous.lean"
**[DataTypesAsLattices/Retracts/treeF.lean](../Retracts/treeF.lean)**

@import "../Retracts/treeF.lean"
**[DataTypesAsLattices/Retracts/lambF.lean](../Retracts/lambF.lean)**

@import "../Retracts/lambF.lean"
**[DataTypesAsLattices/Retracts/lambR.lean](../Retracts/lambR.lean)**

@import "../Retracts/lambR.lean"
**[DataTypesAsLattices/Functionality/envR_map_isScottContinuous.lean](envR_map_isScottContinuous.lean)**

@import "envR_map_isScottContinuous.lean"
**[DataTypesAsLattices/Retracts/envR.lean](../Retracts/envR.lean)**

@import "../Retracts/envR.lean"
**[DataTypesAsLattices/Functionality/envR_app.lean](envR_app.lean)**

@import "envR_app.lean"
**[DataTypesAsLattices/Functionality/continuous_on_diag.lean](continuous_on_diag.lean)**

@import "continuous_on_diag.lean"
**[DataTypesAsLattices/Functionality/continuous_tuple.lean](continuous_tuple.lean)**

@import "continuous_tuple.lean"
**[DataTypesAsLattices/Functionality/arrowR_diag_isScottContinuous.lean](arrowR_diag_isScottContinuous.lean)**

@import "arrowR_diag_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/continuous_nary.lean](continuous_nary.lean)**

@import "continuous_nary.lean"
**[DataTypesAsLattices/Functionality/sumMed.lean](sumMed.lean)**

@import "sumMed.lean"
**[DataTypesAsLattices/Functionality/plus7_map_isScottContinuous.lean](plus7_map_isScottContinuous.lean)**

@import "plus7_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/plus7_comp_isScottContinuous.lean](plus7_comp_isScottContinuous.lean)**

@import "plus7_comp_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/tensorR_diag_isScottContinuous.lean](tensorR_diag_isScottContinuous.lean)**

@import "tensorR_diag_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/treeF_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/treeF_isScottContinuous.lean)**

@import "treeF_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/seq4_body_isScottContinuous.lean](seq4_body_isScottContinuous.lean)**

@import "seq4_body_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/plusR_map_isScottContinuous.lean](plusR_map_isScottContinuous.lean)**

@import "plusR_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/Scomb_inner_isScottContinuous.lean](Scomb_inner_isScottContinuous.lean)**

@import "Scomb_inner_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/Scomb_app2_isGraph.lean](Scomb_app2_isGraph.lean)**

@import "Scomb_app2_isGraph.lean"
**[DataTypesAsLattices/Functionality/outrightC.lean](outrightC.lean)**

@import "outrightC.lean"
**[DataTypesAsLattices/Functionality/plusR_app.lean](plusR_app.lean)**

@import "plusR_app.lean"
**[DataTypesAsLattices/Functionality/plusR_typed_top.lean](plusR_typed_top.lean)**

@import "plusR_typed_top.lean"
**[DataTypesAsLattices/Functionality/plusR_typed_bot.lean](plusR_typed_bot.lean)**

@import "plusR_typed_bot.lean"
**[DataTypesAsLattices/Functionality/plusR_isStrict.lean](plusR_isStrict.lean)**

@import "plusR_isStrict.lean"
**[DataTypesAsLattices/Functionality/plusR_isRetract.lean](plusR_isRetract.lean)**

@import "plusR_isRetract.lean"
**[DataTypesAsLattices/Functionality/outleftC.lean](outleftC.lean)**

@import "outleftC.lean"
**[DataTypesAsLattices/Functionality/plus7_app.lean](plus7_app.lean)**

@import "plus7_app.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl5.lean](plus7_typed_inl5.lean)**

@import "plus7_typed_inl5.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl3.lean](plus7_typed_inl3.lean)**

@import "plus7_typed_inl3.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl2.lean](plus7_typed_inl2.lean)**

@import "plus7_typed_inl2.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl4.lean](plus7_typed_inl4.lean)**

@import "plus7_typed_inl4.lean"
**[DataTypesAsLattices/Functionality/plus7_isRetract.lean](plus7_isRetract.lean)**

@import "plus7_isRetract.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl6.lean](plus7_typed_inl6.lean)**

@import "plus7_typed_inl6.lean"
**[DataTypesAsLattices/Functionality/Scomb_app3.lean](Scomb_app3.lean)**

@import "Scomb_app3.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl0.lean](plus7_typed_inl0.lean)**

@import "plus7_typed_inl0.lean"
**[DataTypesAsLattices/Functionality/plusR_fst.lean](plusR_fst.lean)**

@import "plusR_fst.lean"
**[DataTypesAsLattices/Functionality/plusR_typed_inr.lean](plusR_typed_inr.lean)**

@import "plusR_typed_inr.lean"
**[DataTypesAsLattices/Functionality/Z.lean](Z.lean)**

@import "Z.lean"
**[DataTypesAsLattices/Functionality/plotkin_finite_separation.lean](plotkin_finite_separation.lean)**

@import "plotkin_finite_separation.lean"
**[DataTypesAsLattices/Functionality/finite_sigma_plain_app.lean](finite_sigma_plain_app.lean)**

@import "finite_sigma_plain_app.lean"
**[DataTypesAsLattices/Functionality/plotkinRel.lean](plotkinRel.lean)**

@import "plotkinRel.lean"
**[DataTypesAsLattices/Functionality/plotkinGood.lean](plotkinGood.lean)**

@import "plotkinGood.lean"
**[DataTypesAsLattices/Functionality/eraseTag.lean](eraseTag.lean)**

@import "eraseTag.lean"
**[DataTypesAsLattices/Functionality/eq_7_18_eq.lean](eq_7_18_eq.lean)**

@import "eq_7_18_eq.lean"
**[DataTypesAsLattices/Functionality/eq_7_19.lean](eq_7_19.lean)**

@import "eq_7_19.lean"
**[DataTypesAsLattices/Functionality/Zcomb.lean](Zcomb.lean)**

@import "Zcomb.lean"
**[DataTypesAsLattices/Enumeration/Gcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb.lean)**

@import "../Enumeration/Gcomb.lean"
**[DataTypesAsLattices/Enumeration/not_mem_zero_Gcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/not_mem_zero_Gcomb.lean)**

@import "../Enumeration/not_mem_zero_Gcomb.lean"
**[DataTypesAsLattices/Enumeration/Gcomb_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb_more.lean)**

@import "../Enumeration/Gcomb_more.lean"
**[DataTypesAsLattices/Enumeration/Scomb_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/Scomb_from_G.lean)**

@import "../Enumeration/Scomb_from_G.lean"
**[DataTypesAsLattices/Enumeration/Kcomb_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/Kcomb_from_G.lean)**

@import "../Enumeration/Kcomb_from_G.lean"
**[DataTypesAsLattices/Enumeration/valNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat.lean)**

@import "../Enumeration/valNat.lean"
**[DataTypesAsLattices/Enumeration/condC_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/condC_from_G.lean)**

@import "../Enumeration/condC_from_G.lean"
**[DataTypesAsLattices/Enumeration/sucC_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/sucC_from_G.lean)**

@import "../Enumeration/sucC_from_G.lean"
**[DataTypesAsLattices/Enumeration/ValTrace.lean](DomainTheory/DataTypesAsLattices/Enumeration/ValTrace.lean)**

@import "../Enumeration/ValTrace.lean"
**[DataTypesAsLattices/Enumeration/valTraceG.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceG.lean)**

@import "../Enumeration/valTraceG.lean"
**[DataTypesAsLattices/Enumeration/valTraceHas.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceHas.lean)**

@import "../Enumeration/valTraceHas.lean"
**[DataTypesAsLattices/Enumeration/gClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/gClosed.lean)**

@import "../Enumeration/gClosed.lean"
**[DataTypesAsLattices/Enumeration/Subalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/Subalgebra.lean)**

@import "../Enumeration/Subalgebra.lean"
**[DataTypesAsLattices/Enumeration/GeneratedSubalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedSubalgebra.lean)**

@import "../Enumeration/GeneratedSubalgebra.lean"
**[DataTypesAsLattices/Enumeration/realizes_valNat_mem.lean](DomainTheory/DataTypesAsLattices/Enumeration/realizes_valNat_mem.lean)**

@import "../Enumeration/realizes_valNat_mem.lean"
**[DataTypesAsLattices/Enumeration/GeneratedFromG.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedFromG.lean)**

@import "../Enumeration/GeneratedFromG.lean"
**[DataTypesAsLattices/Enumeration/Deg.lean](DomainTheory/DataTypesAsLattices/Enumeration/Deg.lean)**

@import "../Enumeration/Deg.lean"
**[DataTypesAsLattices/Enumeration/predC_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/predC_from_G.lean)**

@import "../Enumeration/predC_from_G.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_1.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_1.lean)**

@import "../Enumeration/theorem_3_1.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_2.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_2.lean)**

@import "../Enumeration/theorem_3_2.lean"
**[DataTypesAsLattices/Enumeration/secondRecOperatorCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecOperatorCode.lean)**

@import "../Enumeration/secondRecOperatorCode.lean"
**[DataTypesAsLattices/Enumeration/unionCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionCode.lean)**

@import "../Enumeration/unionCode.lean"
**[DataTypesAsLattices/Enumeration/Ycode.lean](DomainTheory/DataTypesAsLattices/Enumeration/Ycode.lean)**

@import "../Enumeration/Ycode.lean"
**[DataTypesAsLattices/Enumeration/botCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/botCode.lean)**

@import "../Enumeration/botCode.lean"
**[DataTypesAsLattices/Enumeration/finAux.lean](DomainTheory/DataTypesAsLattices/Enumeration/finAux.lean)**

@import "../Enumeration/finAux.lean"
**[DataTypesAsLattices/Enumeration/interCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/interCode.lean)**

@import "../Enumeration/interCode.lean"
**[DataTypesAsLattices/Enumeration/fin.lean](DomainTheory/DataTypesAsLattices/Enumeration/fin.lean)**

@import "../Enumeration/fin.lean"
**[DataTypesAsLattices/Computability/theorem_2_6.lean](DomainTheory/DataTypesAsLattices/Computability/theorem_2_6.lean)**

@import "../Computability/theorem_2_6.lean"
**[DataTypesAsLattices/Enumeration/myhillQ.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillQ.lean)**

@import "../Enumeration/myhillQ.lean"
**[DataTypesAsLattices/Enumeration/combinatory_mem_subalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/combinatory_mem_subalgebra.lean)**

@import "../Enumeration/combinatory_mem_subalgebra.lean"
**[DataTypesAsLattices/Enumeration/seq2_mem_subalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_mem_subalgebra.lean)**

@import "../Enumeration/seq2_mem_subalgebra.lean"
**[DataTypesAsLattices/Enumeration/secondRecV.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecV.lean)**

@import "../Enumeration/secondRecV.lean"
**[DataTypesAsLattices/Enumeration/primrec_secondRecV.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_secondRecV.lean)**

@import "../Enumeration/primrec_secondRecV.lean"
**[DataTypesAsLattices/Enumeration/combinatory_mem_Deg.lean](DomainTheory/DataTypesAsLattices/Enumeration/combinatory_mem_Deg.lean)**

@import "../Enumeration/combinatory_mem_Deg.lean"
**[DataTypesAsLattices/Enumeration/packList.lean](DomainTheory/DataTypesAsLattices/Enumeration/packList.lean)**

@import "../Enumeration/packList.lean"
**[DataTypesAsLattices/Enumeration/diagonalInterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/diagonalInterCode.lean)**

@import "../Enumeration/diagonalInterCode.lean"
**[DataTypesAsLattices/Enumeration/primrec_diagonalInterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_diagonalInterCode.lean)**

@import "../Enumeration/primrec_diagonalInterCode.lean"
**[DataTypesAsLattices/Enumeration/singleGenerator.lean](DomainTheory/DataTypesAsLattices/Enumeration/singleGenerator.lean)**

@import "../Enumeration/singleGenerator.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_6.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_6.lean)**

@import "../Enumeration/theorem_3_6.lean"
**[DataTypesAsLattices/Enumeration/generators_mem_singleGenerator_degree.lean](DomainTheory/DataTypesAsLattices/Enumeration/generators_mem_singleGenerator_degree.lean)**

@import "../Enumeration/generators_mem_singleGenerator_degree.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_6_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_6_more.lean)**

@import "../Enumeration/theorem_3_6_more.lean"
**[DataTypesAsLattices/Enumeration/primrecu2082_finAux.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecu2082_finAux.lean)**

@import "../Enumeration/primrecu2082_finAux.lean"
**[DataTypesAsLattices/Enumeration/vaalF.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalF.lean)**

@import "../Enumeration/vaalF.lean"
**[DataTypesAsLattices/Enumeration/vaalStepTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalStepTerm.lean)**

@import "../Enumeration/vaalStepTerm.lean"
**[DataTypesAsLattices/Enumeration/primrecRel_valTraceHas.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecRel_valTraceHas.lean)**

@import "../Enumeration/primrecRel_valTraceHas.lean"
**[DataTypesAsLattices/Enumeration/Lcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lcomb.lean)**

@import "../Enumeration/Lcomb.lean"
**[DataTypesAsLattices/Enumeration/valStep.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStep.lean)**

@import "../Enumeration/valStep.lean"
**[DataTypesAsLattices/Enumeration/valStage_subset.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStage_subset.lean)**

@import "../Enumeration/valStage_subset.lean"
**[DataTypesAsLattices/Enumeration/Gbar.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gbar.lean)**

@import "../Enumeration/Gbar.lean"
**[DataTypesAsLattices/Enumeration/GeneratedSemigroup.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedSemigroup.lean)**

@import "../Enumeration/GeneratedSemigroup.lean"
**[DataTypesAsLattices/Enumeration/haltEnum.lean](DomainTheory/DataTypesAsLattices/Enumeration/haltEnum.lean)**

@import "../Enumeration/haltEnum.lean"
**[DataTypesAsLattices/Enumeration/primrec_haltEnum.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_haltEnum.lean)**

@import "../Enumeration/primrec_haltEnum.lean"
**[DataTypesAsLattices/Enumeration/haltEnum_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/haltEnum_more.lean)**

@import "../Enumeration/haltEnum_more.lean"
**[DataTypesAsLattices/Enumeration/Lterm.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lterm.lean)**

@import "../Enumeration/Lterm.lean"
**[DataTypesAsLattices/Enumeration/beforeHalt.lean](DomainTheory/DataTypesAsLattices/Enumeration/beforeHalt.lean)**

@import "../Enumeration/beforeHalt.lean"
**[DataTypesAsLattices/Enumeration/BasicInst85.lean](DomainTheory/DataTypesAsLattices/Enumeration/BasicInst85.lean)**

@import "../Enumeration/BasicInst85.lean"
**[DataTypesAsLattices/Enumeration/Lterm_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lterm_more.lean)**

@import "../Enumeration/Lterm_more.lean"
**[DataTypesAsLattices/Enumeration/Lcomb_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lcomb_more.lean)**

@import "../Enumeration/Lcomb_more.lean"
**[DataTypesAsLattices/Enumeration/generatedSemigroup_mem_RE_FUN.lean](DomainTheory/DataTypesAsLattices/Enumeration/generatedSemigroup_mem_RE_FUN.lean)**

@import "../Enumeration/generatedSemigroup_mem_RE_FUN.lean"
**[DataTypesAsLattices/Enumeration/filterNum.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterNum.lean)**

@import "../Enumeration/filterNum.lean"
**[DataTypesAsLattices/Enumeration/primrecPred_beforeHalt.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecPred_beforeHalt.lean)**

@import "../Enumeration/primrecPred_beforeHalt.lean"
**[DataTypesAsLattices/Enumeration/primrec_filterNum.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_filterNum.lean)**

@import "../Enumeration/primrec_filterNum.lean"
**[DataTypesAsLattices/Enumeration/eq_3_16.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_16.lean)**

@import "../Enumeration/eq_3_16.lean"
**[DataTypesAsLattices/Enumeration/eq_3_17.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_17.lean)**

@import "../Enumeration/eq_3_17.lean"
**[DataTypesAsLattices/Enumeration/bar_generated.lean](DomainTheory/DataTypesAsLattices/Enumeration/bar_generated.lean)**

@import "../Enumeration/bar_generated.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_7.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_7.lean)**

@import "../Enumeration/theorem_3_7.lean"
**[DataTypesAsLattices/Enumeration/filterRealizer.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterRealizer.lean)**

@import "../Enumeration/filterRealizer.lean"
**[DataTypesAsLattices/Enumeration/filterSeq_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterSeq_isScottContinuous.lean)**

@import "../Enumeration/filterSeq_isScottContinuous.lean"
**[DataTypesAsLattices/Enumeration/filterTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterTerm.lean)**

@import "../Enumeration/filterTerm.lean"
**[DataTypesAsLattices/Enumeration/filterEnv.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterEnv.lean)**

@import "../Enumeration/filterEnv.lean"
**[DataTypesAsLattices/Enumeration/filterC.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterC.lean)**

@import "../Enumeration/filterC.lean"
**[DataTypesAsLattices/Enumeration/filterOp.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterOp.lean)**

@import "../Enumeration/filterOp.lean"
**[DataTypesAsLattices/Enumeration/myhillFilterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillFilterCode.lean)**

@import "../Enumeration/myhillFilterCode.lean"
**[DataTypesAsLattices/Enumeration/primrec_myhillFilterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_myhillFilterCode.lean)**

@import "../Enumeration/primrec_myhillFilterCode.lean"
**[DataTypesAsLattices/Enumeration/eq_3_8_val.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_8_val.lean)**

@import "../Enumeration/eq_3_8_val.lean"
**[DataTypesAsLattices/Enumeration/eq_3_9_val.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_9_val.lean)**

@import "../Enumeration/eq_3_9_val.lean"
**[DataTypesAsLattices/Enumeration/mem_myhillQ.lean](DomainTheory/DataTypesAsLattices/Enumeration/mem_myhillQ.lean)**

@import "../Enumeration/mem_myhillQ.lean"
**[DataTypesAsLattices/Enumeration/condCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/condCode.lean)**

@import "../Enumeration/condCode.lean"
**[DataTypesAsLattices/Enumeration/myhillCase2Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillCase2Code.lean)**

@import "../Enumeration/myhillCase2Code.lean"
**[DataTypesAsLattices/Enumeration/primrec_myhillCase2Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_myhillCase2Code.lean)**

@import "../Enumeration/primrec_myhillCase2Code.lean"
**[DataTypesAsLattices/Enumeration/myhillCase1Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillCase1Code.lean)**

@import "../Enumeration/myhillCase1Code.lean"
**[DataTypesAsLattices/Enumeration/primrec_myhillCase1Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_myhillCase1Code.lean)**

@import "../Enumeration/primrec_myhillCase1Code.lean"
**[DataTypesAsLattices/Enumeration/primrec_fin.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_fin.lean)**

@import "../Enumeration/primrec_fin.lean"
**[DataTypesAsLattices/Enumeration/eq_3_10_val.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_10_val.lean)**

@import "../Enumeration/eq_3_10_val.lean"
**[DataTypesAsLattices/Enumeration/valEntryJustified.lean](DomainTheory/DataTypesAsLattices/Enumeration/valEntryJustified.lean)**

@import "../Enumeration/valEntryJustified.lean"
**[DataTypesAsLattices/Enumeration/primrecPred_valEntryJustified.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecPred_valEntryJustified.lean)**

@import "../Enumeration/primrecPred_valEntryJustified.lean"
**[DataTypesAsLattices/Enumeration/valTraceStruct.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceStruct.lean)**

@import "../Enumeration/valTraceStruct.lean"
**[DataTypesAsLattices/Enumeration/primrecPred_valTraceStruct.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecPred_valTraceStruct.lean)**

@import "../Enumeration/primrecPred_valTraceStruct.lean"
**[DataTypesAsLattices/Enumeration/valTraceOk.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk.lean)**

@import "../Enumeration/valTraceOk.lean"
**[DataTypesAsLattices/Enumeration/exists_concat_traces.lean](DomainTheory/DataTypesAsLattices/Enumeration/exists_concat_traces.lean)**

@import "../Enumeration/exists_concat_traces.lean"
**[DataTypesAsLattices/Enumeration/valTraceOk_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk_more.lean)**

@import "../Enumeration/valTraceOk_more.lean"
**[DataTypesAsLattices/Enumeration/recCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/recCode.lean)**

@import "../Enumeration/recCode.lean"
**[DataTypesAsLattices/Enumeration/eq_3_12.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_12.lean)**

@import "../Enumeration/eq_3_12.lean"
**[DataTypesAsLattices/Enumeration/valStage_eq_of_rank_le.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStage_eq_of_rank_le.lean)**

@import "../Enumeration/valStage_eq_of_rank_le.lean"
**[DataTypesAsLattices/Enumeration/valC.lean](DomainTheory/DataTypesAsLattices/Enumeration/valC.lean)**

@import "../Enumeration/valC.lean"
**[DataTypesAsLattices/Functionality/plotkinE.lean](plotkinE.lean)**

@import "plotkinE.lean"
**[DataTypesAsLattices/Functionality/iterateE.lean](iterateE.lean)**

@import "iterateE.lean"
**[DataTypesAsLattices/Functionality/evalC_isScottContinuous.lean](evalC_isScottContinuous.lean)**

@import "evalC_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/evalC_app.lean](evalC_app.lean)**

@import "evalC_app.lean"
**[DataTypesAsLattices/Functionality/seq4_comp_isScottContinuous.lean](seq4_comp_isScottContinuous.lean)**

@import "seq4_comp_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/tensor4_map_isScottContinuous.lean](tensor4_map_isScottContinuous.lean)**

@import "tensor4_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/tensor4_diag_isScottContinuous.lean](tensor4_diag_isScottContinuous.lean)**

@import "tensor4_diag_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/expF_isScottContinuous.lean](expF_isScottContinuous.lean)**

@import "expF_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/eq_4_44.lean](eq_4_44.lean)**

@import "eq_4_44.lean"
**[DataTypesAsLattices/Functionality/tensor4_app.lean](tensor4_app.lean)**

@import "tensor4_app.lean"
**[DataTypesAsLattices/Functionality/eq_4_13.lean](eq_4_13.lean)**

@import "eq_4_13.lean"
**[DataTypesAsLattices/Functionality/eq_7_18_ne.lean](eq_7_18_ne.lean)**

@import "eq_7_18_ne.lean"
**[DataTypesAsLattices/Functionality/lambF_isScottContinuous.lean](lambF_isScottContinuous.lean)**

@import "lambF_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/seq4_app.lean](seq4_app.lean)**

@import "seq4_app.lean"
**[DataTypesAsLattices/Functionality/tensor4_isRetract.lean](tensor4_isRetract.lean)**

@import "tensor4_isRetract.lean"
**[DataTypesAsLattices/Functionality/diagC_app.lean](diagC_app.lean)**

@import "diagC_app.lean"
**[DataTypesAsLattices/Functionality/plus7_typed_inl1.lean](plus7_typed_inl1.lean)**

@import "plus7_typed_inl1.lean"
**[DataTypesAsLattices/Functionality/theorem_7_1.lean](theorem_7_1.lean)**

@import "theorem_7_1.lean"
**[DataTypesAsLattices/Functionality/theorem_7_3.lean](theorem_7_3.lean)**

@import "theorem_7_3.lean"
**[DataTypesAsLattices/Functionality/plusR_typed_inl.lean](plusR_typed_inl.lean)**

@import "plusR_typed_inl.lean"
**[DataTypesAsLattices/Functionality/plusR_typed_iff.lean](plusR_typed_iff.lean)**

@import "plusR_typed_iff.lean"
**[DataTypesAsLattices/Functionality/theorem_4_5_sum.lean](theorem_4_5_sum.lean)**

@import "theorem_4_5_sum.lean"
**[DataTypesAsLattices/Functionality/normalized_finite_fresh_app.lean](normalized_finite_fresh_app.lean)**

@import "normalized_finite_fresh_app.lean"
**[DataTypesAsLattices/Functionality/finite_sigma_union_app.lean](finite_sigma_union_app.lean)**

@import "finite_sigma_union_app.lean"
**[DataTypesAsLattices/Functionality/plotkin_function_related.lean](plotkin_function_related.lean)**

@import "plotkin_function_related.lean"
**[DataTypesAsLattices/Functionality/tensorR_map_isScottContinuous.lean](tensorR_map_isScottContinuous.lean)**

@import "tensorR_map_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/tensorR_app.lean](tensorR_app.lean)**

@import "tensorR_app.lean"
**[DataTypesAsLattices/Functionality/typed_pairSeq_tensorR.lean](typed_pairSeq_tensorR.lean)**

@import "typed_pairSeq_tensorR.lean"
**[DataTypesAsLattices/Functionality/tensorR_isRetract.lean](tensorR_isRetract.lean)**

@import "tensorR_isRetract.lean"
**[DataTypesAsLattices/Functionality/theorem_4_4_typed.lean](theorem_4_4_typed.lean)**

@import "theorem_4_4_typed.lean"
**[DataTypesAsLattices/Functionality/eq_4_20.lean](eq_4_20.lean)**

@import "eq_4_20.lean"
**[DataTypesAsLattices/Functionality/eq_4_12.lean](eq_4_12.lean)**

@import "eq_4_12.lean"
**[DataTypesAsLattices/Functionality/eq_4_21.lean](eq_4_21.lean)**

@import "eq_4_21.lean"
**[DataTypesAsLattices/Retracts/treeR.lean](../Retracts/treeR.lean)**

@import "../Retracts/treeR.lean"
**[DataTypesAsLattices/Functionality/eq_4_38.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_38.lean)**

@import "eq_4_38.lean"
**[DataTypesAsLattices/Retracts/inverseLimit_iUnion_typed.lean](../Retracts/inverseLimit_iUnion_typed.lean)**

@import "../Retracts/inverseLimit_iUnion_typed.lean"
**[DataTypesAsLattices/Retracts/inverseLimitToFixed.lean](../Retracts/inverseLimitToFixed.lean)**

@import "../Retracts/inverseLimitToFixed.lean"
**[DataTypesAsLattices/Retracts/theorem_4_6.lean](../Retracts/theorem_4_6.lean)**

@import "../Retracts/theorem_4_6.lean"
**[DataTypesAsLattices/Functionality/treeR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/treeR_isRetract.lean)**

@import "treeR_isRetract.lean"
**[DataTypesAsLattices/Functionality/expR_isRetract.lean](expR_isRetract.lean)**

@import "expR_isRetract.lean"
**[DataTypesAsLattices/Retracts/theorem_4_3_more.lean](../Retracts/theorem_4_3_more.lean)**

@import "../Retracts/theorem_4_3_more.lean"
**[DataTypesAsLattices/Retracts/arrowR_more.lean](../Retracts/arrowR_more.lean)**

@import "../Retracts/arrowR_more.lean"
**[DataTypesAsLattices/Enumeration/vaalC.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalC.lean)**

@import "../Enumeration/vaalC.lean"
**[DataTypesAsLattices/Enumeration/vaalTyped.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalTyped.lean)**

@import "../Enumeration/vaalTyped.lean"
**[DataTypesAsLattices/Enumeration/valNat_codes.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_codes.lean)**

@import "../Enumeration/valNat_codes.lean"
**[DataTypesAsLattices/Enumeration/myhillQ_more.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillQ_more.lean)**

@import "../Enumeration/myhillQ_more.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_4.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_4.lean)**

@import "../Enumeration/theorem_3_4.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_5.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_5.lean)**

@import "../Enumeration/theorem_3_5.lean"
**[DataTypesAsLattices/Enumeration/theorem_3_3.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_3.lean)**

@import "../Enumeration/theorem_3_3.lean"
**[DataTypesAsLattices/Functionality/eq_4_19.lean](eq_4_19.lean)**

@import "eq_4_19.lean"
**[DataTypesAsLattices/Functionality/eq_4_33.lean](eq_4_33.lean)**

@import "eq_4_33.lean"
**[DataTypesAsLattices/Functionality/typed_isGraph.lean](typed_isGraph.lean)**

@import "typed_isGraph.lean"
**[DataTypesAsLattices/Functionality/eq_4_34.lean](eq_4_34.lean)**

@import "eq_4_34.lean"
**[DataTypesAsLattices/Functionality/lambR_isRetract.lean](lambR_isRetract.lean)**

@import "lambR_isRetract.lean"
**[DataTypesAsLattices/Retracts/typed_more.lean](../Retracts/typed_more.lean)**

@import "../Retracts/typed_more.lean"
**[DataTypesAsLattices/Retracts/theorem_4_3.lean](../Retracts/theorem_4_3.lean)**

@import "../Retracts/theorem_4_3.lean"
**[DataTypesAsLattices/Closures/theorem_5_3.lean](../Closures/theorem_5_3.lean)**

@import "../Closures/theorem_5_3.lean"
**[DataTypesAsLattices/Closures/theorem_5_6.lean](../Closures/theorem_5_6.lean)**

@import "../Closures/theorem_5_6.lean"
**[DataTypesAsLattices/Functionality/theorem_7_2.lean](theorem_7_2.lean)**

@import "theorem_7_2.lean"
**[DataTypesAsLattices/Closures/eq_5_24.lean](../Closures/eq_5_24.lean)**

@import "../Closures/eq_5_24.lean"
**[DataTypesAsLattices/Functionality/eq_4_32.lean](eq_4_32.lean)**

@import "eq_4_32.lean"
**[DataTypesAsLattices/Functionality/theorem_4_4_med.lean](theorem_4_4_med.lean)**

@import "theorem_4_4_med.lean"
**[DataTypesAsLattices/Functionality/theorem_4_4_med_unique.lean](theorem_4_4_med_unique.lean)**

@import "theorem_4_4_med_unique.lean"
**[DataTypesAsLattices/Functionality/eq_4_18.lean](eq_4_18.lean)**

@import "eq_4_18.lean"
**[DataTypesAsLattices/Functionality/eq_4_35.lean](eq_4_35.lean)**

@import "eq_4_35.lean"
**[DataTypesAsLattices/Functionality/eq_4_17.lean](eq_4_17.lean)**

@import "eq_4_17.lean"
**[DataTypesAsLattices/Functionality/eq_4_24.lean](eq_4_24.lean)**

@import "eq_4_24.lean"
**[DataTypesAsLattices/Functionality/eq_4_37.lean](eq_4_37.lean)**

@import "eq_4_37.lean"
**[DataTypesAsLattices/Functionality/eq_4_25.lean](eq_4_25.lean)**

@import "eq_4_25.lean"
**[DataTypesAsLattices/Functionality/envR_isRetract.lean](envR_isRetract.lean)**

@import "envR_isRetract.lean"
**[DataTypesAsLattices/Functionality/eq_4_36.lean](eq_4_36.lean)**

@import "eq_4_36.lean"
**[DataTypesAsLattices/Functionality/eq_4_39.lean](eq_4_39.lean)**

@import "eq_4_39.lean"
**[DataTypesAsLattices/Functionality/LambTerm.lean](LambTerm.lean)**

@import "LambTerm.lean"
**[DataTypesAsLattices/Functionality/encodeExp.lean](encodeExp.lean)**

@import "encodeExp.lean"
**[DataTypesAsLattices/Functionality/encodeExp_typed.lean](encodeExp_typed.lean)**

@import "encodeExp_typed.lean"
**[DataTypesAsLattices/Functionality/Hinterp.lean](Hinterp.lean)**

@import "Hinterp.lean"
**[DataTypesAsLattices/Functionality/Htyped.lean](Htyped.lean)**

@import "Htyped.lean"
**[DataTypesAsLattices/Functionality/hApply.lean](hApply.lean)**

@import "hApply.lean"
**[DataTypesAsLattices/Functionality/hCond.lean](hCond.lean)**

@import "hCond.lean"
**[DataTypesAsLattices/Functionality/hPred.lean](hPred.lean)**

@import "hPred.lean"
**[DataTypesAsLattices/Functionality/hApp.lean](hApp.lean)**

@import "hApp.lean"
**[DataTypesAsLattices/Functionality/hLam.lean](hLam.lean)**

@import "hLam.lean"
**[DataTypesAsLattices/Functionality/hSucc.lean](hSucc.lean)**

@import "hSucc.lean"
**[DataTypesAsLattices/Functionality/Hstep.lean](Hstep.lean)**

@import "Hstep.lean"
**[DataTypesAsLattices/Functionality/HF.lean](HF.lean)**

@import "HF.lean"
**[DataTypesAsLattices/Functionality/Hfun.lean](Hfun.lean)**

@import "Hfun.lean"
**[DataTypesAsLattices/Functionality/Hcomb.lean](Hcomb.lean)**

@import "Hcomb.lean"
**[DataTypesAsLattices/Functionality/theorem_7_4.lean](theorem_7_4.lean)**

@import "theorem_7_4.lean"
**[DataTypesAsLattices/Functionality/eq_4_45.lean](eq_4_45.lean)**

@import "eq_4_45.lean"
