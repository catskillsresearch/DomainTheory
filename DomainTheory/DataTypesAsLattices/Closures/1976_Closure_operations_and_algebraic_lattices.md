# Closure operations and algebraic lattices

## Historical note

Algebraic lattices and closure operations predate the paper: Grätzer (1968) for the lattices, Tarski (1930) for the closures. Per Martin-Löf and Peter Hancock suggested that the continuous closures form a universe, and the construction of $\mathbf{V}$ is essentially theirs. The limit theorem is Scott's.

**Dependencies.** Inside Closures, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Closures.mermaid"

@import "1976_Closure_operations_and_algebraic_lattices.english" {code_block=false}

**[DataTypesAsLattices/Closures/Icomb_isClosure.lean](Icomb_isClosure.lean)**

@import "Icomb_isClosure.lean"

**[DataTypesAsLattices/Closures/Icomb_subset_graph.lean](Icomb_subset_graph.lean)**

@import "Icomb_subset_graph.lean"

**[DataTypesAsLattices/Closures/Icomb_subset_intR.lean](Icomb_subset_intR.lean)**

@import "Icomb_subset_intR.lean"

**[DataTypesAsLattices/Closures/Closure.lean](Closure.lean)**

@import "Closure.lean"

**[DataTypesAsLattices/Closures/Isolated.lean](Isolated.lean)**

@import "Isolated.lean"

**[DataTypesAsLattices/Closures/Vapply.lean](Vapply.lean)**

@import "Vapply.lean"

**[DataTypesAsLattices/Closures/Vcomb.lean](Vcomb.lean)**

@import "Vcomb.lean"

**[DataTypesAsLattices/Closures/Vstep.lean](Vstep.lean)**

@import "Vstep.lean"

**[DataTypesAsLattices/Closures/VapplyY.lean](VapplyY.lean)**

@import "VapplyY.lean"

**[DataTypesAsLattices/Closures/arrowR_diag_isScottContinuous.lean](arrowR_diag_isScottContinuous.lean)**

@import "arrowR_diag_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/boool.lean](boool.lean)**

@import "boool.lean"

**[DataTypesAsLattices/Closures/boool_expansive.lean](boool_expansive.lean)**

@import "boool_expansive.lean"

**[DataTypesAsLattices/Closures/Icomb_subset_boool.lean](Icomb_subset_boool.lean)**

@import "Icomb_subset_boool.lean"

**[DataTypesAsLattices/Closures/boool_idem.lean](boool_idem.lean)**

@import "boool_idem.lean"

**[DataTypesAsLattices/Closures/boool_map_isScottContinuous.lean](boool_map_isScottContinuous.lean)**

@import "boool_map_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/boool_app.lean](boool_app.lean)**

@import "boool_app.lean"

**[DataTypesAsLattices/Closures/boool_isRetract.lean](boool_isRetract.lean)**

@import "boool_isRetract.lean"

**[DataTypesAsLattices/Closures/boool_isClosure.lean](boool_isClosure.lean)**

@import "boool_isClosure.lean"

**[DataTypesAsLattices/Closures/botElem_union.lean](botElem_union.lean)**

@import "botElem_union.lean"

**[DataTypesAsLattices/Closures/boxShift.lean](boxShift.lean)**

@import "boxShift.lean"

**[DataTypesAsLattices/Closures/boxTag.lean](boxTag.lean)**

@import "boxTag.lean"

**[DataTypesAsLattices/Closures/boxTag_bot.lean](boxTag_bot.lean)**

@import "boxTag_bot.lean"

**[DataTypesAsLattices/Closures/boxTag_isScottContinuous.lean](boxTag_isScottContinuous.lean)**

@import "boxTag_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/boxTag_of_mem.lean](boxTag_of_mem.lean)**

@import "boxTag_of_mem.lean"

**[DataTypesAsLattices/Closures/closureCompact.lean](closureCompact.lean)**

@import "closureCompact.lean"

**[DataTypesAsLattices/Closures/closure_expansive.lean](closure_expansive.lean)**

@import "closure_expansive.lean"

**[DataTypesAsLattices/Closures/closureCompact_isCompact.lean](closureCompact_isCompact.lean)**

@import "closureCompact_isCompact.lean"

**[DataTypesAsLattices/Closures/compactFixedBelow.lean](compactFixedBelow.lean)**

@import "compactFixedBelow.lean"

**[DataTypesAsLattices/Closures/compactFixedBelow_directedSubset.lean](compactFixedBelow_directedSubset.lean)**

@import "compactFixedBelow_directedSubset.lean"

**[DataTypesAsLattices/Closures/compactFixedBelow_sUnion.lean](compactFixedBelow_sUnion.lean)**

@import "compactFixedBelow_sUnion.lean"

**[DataTypesAsLattices/Closures/compact_fixed_iff.lean](compact_fixed_iff.lean)**

@import "compact_fixed_iff.lean"

**[DataTypesAsLattices/Closures/directed_finite_cover_subset.lean](directed_finite_cover_subset.lean)**

@import "directed_finite_cover_subset.lean"

**[DataTypesAsLattices/Closures/closureCompact_isCompactSubset.lean](closureCompact_isCompactSubset.lean)**

@import "closureCompact_isCompactSubset.lean"

**[DataTypesAsLattices/Closures/compact_fixed_iff_subset.lean](compact_fixed_iff_subset.lean)**

@import "compact_fixed_iff_subset.lean"

**[DataTypesAsLattices/Closures/eq_5_1.lean](eq_5_1.lean)**

@import "eq_5_1.lean"

**[DataTypesAsLattices/Closures/Icomb_subset_funRetract.lean](Icomb_subset_funRetract.lean)**

@import "Icomb_subset_funRetract.lean"

**[DataTypesAsLattices/Closures/eq_5_10.lean](eq_5_10.lean)**

@import "eq_5_10.lean"

**[DataTypesAsLattices/Closures/eq_5_11.lean](eq_5_11.lean)**

@import "eq_5_11.lean"

**[DataTypesAsLattices/Closures/Icomb_subset_arrowR.lean](Icomb_subset_arrowR.lean)**

@import "Icomb_subset_arrowR.lean"

**[DataTypesAsLattices/Closures/eq_5_12.lean](eq_5_12.lean)**

@import "eq_5_12.lean"

**[DataTypesAsLattices/Closures/eq_5_13.lean](eq_5_13.lean)**

@import "eq_5_13.lean"

**[DataTypesAsLattices/Closures/eq_5_16.lean](eq_5_16.lean)**

@import "eq_5_16.lean"

**[DataTypesAsLattices/Closures/Vapply_eq_imp_expansive.lean](Vapply_eq_imp_expansive.lean)**

@import "Vapply_eq_imp_expansive.lean"

**[DataTypesAsLattices/Closures/Vapply_prefixpoint.lean](Vapply_prefixpoint.lean)**

@import "Vapply_prefixpoint.lean"

**[DataTypesAsLattices/Closures/Vapply_closed.lean](Vapply_closed.lean)**

@import "Vapply_closed.lean"

**[DataTypesAsLattices/Closures/Vapply_eq_Vstep.lean](Vapply_eq_Vstep.lean)**

@import "Vapply_eq_Vstep.lean"

**[DataTypesAsLattices/Closures/eq_5_17.lean](eq_5_17.lean)**

@import "eq_5_17.lean"

**[DataTypesAsLattices/Closures/Vapply_eq_imp_idem.lean](Vapply_eq_imp_idem.lean)**

@import "Vapply_eq_imp_idem.lean"

**[DataTypesAsLattices/Closures/eq_5_18.lean](eq_5_18.lean)**

@import "eq_5_18.lean"

**[DataTypesAsLattices/Closures/eq_5_18_rev.lean](eq_5_18_rev.lean)**

@import "eq_5_18_rev.lean"

**[DataTypesAsLattices/Closures/eq_5_18_eq.lean](eq_5_18_eq.lean)**

@import "eq_5_18_eq.lean"

**[DataTypesAsLattices/Closures/eq_5_2.lean](eq_5_2.lean)**

@import "eq_5_2.lean"

**[DataTypesAsLattices/Closures/eq_5_8.lean](eq_5_8.lean)**

@import "eq_5_8.lean"

**[DataTypesAsLattices/Closures/eq_5_9.lean](eq_5_9.lean)**

@import "eq_5_9.lean"

**[DataTypesAsLattices/Closures/exists_mem_of_ne_bot.lean](exists_mem_of_ne_bot.lean)**

@import "exists_mem_of_ne_bot.lean"

**[DataTypesAsLattices/Closures/funRetract_isClosure.lean](funRetract_isClosure.lean)**

@import "funRetract_isClosure.lean"

**[DataTypesAsLattices/Closures/intR_isClosure.lean](intR_isClosure.lean)**

@import "intR_isClosure.lean"

**[DataTypesAsLattices/Closures/openR_map_isScottContinuous.lean](openR_map_isScottContinuous.lean)**

@import "openR_map_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/openR_app.lean](openR_app.lean)**

@import "openR_app.lean"

**[DataTypesAsLattices/Closures/openR_expansive.lean](openR_expansive.lean)**

@import "openR_expansive.lean"

**[DataTypesAsLattices/Closures/Icomb_subset_openR.lean](Icomb_subset_openR.lean)**

@import "Icomb_subset_openR.lean"

**[DataTypesAsLattices/Closures/openR_idem.lean](openR_idem.lean)**

@import "openR_idem.lean"

**[DataTypesAsLattices/Closures/openR_isRetract.lean](openR_isRetract.lean)**

@import "openR_isRetract.lean"

**[DataTypesAsLattices/Closures/openR_isClosure.lean](openR_isClosure.lean)**

@import "openR_isClosure.lean"

**[DataTypesAsLattices/Closures/predSet_succSet.lean](predSet_succSet.lean)**

@import "predSet_succSet.lean"

**[DataTypesAsLattices/Closures/predSet_union.lean](predSet_union.lean)**

@import "predSet_union.lean"

**[DataTypesAsLattices/Closures/representClosure.lean](representClosure.lean)**

@import "representClosure.lean"

**[DataTypesAsLattices/Closures/representClosureCode.lean](representClosureCode.lean)**

@import "representClosureCode.lean"

**[DataTypesAsLattices/Closures/representClosure_expansive.lean](representClosure_expansive.lean)**

@import "representClosure_expansive.lean"

**[DataTypesAsLattices/Closures/representClosure_idem.lean](representClosure_idem.lean)**

@import "representClosure_idem.lean"

**[DataTypesAsLattices/Closures/representClosureCode_isClosure.lean](representClosureCode_isClosure.lean)**

@import "representClosureCode_isClosure.lean"

**[DataTypesAsLattices/Closures/representClosure_mono.lean](representClosure_mono.lean)**

@import "representClosure_mono.lean"

**[DataTypesAsLattices/Closures/representClosure_isScottContinuous.lean](representClosure_isScottContinuous.lean)**

@import "representClosure_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/representClosureCode_app.lean](representClosureCode_app.lean)**

@import "representClosureCode_app.lean"

**[DataTypesAsLattices/Closures/representationDecode.lean](representationDecode.lean)**

@import "representationDecode.lean"

**[DataTypesAsLattices/Closures/representationEncode.lean](representationEncode.lean)**

@import "representationEncode.lean"

**[DataTypesAsLattices/Closures/representationDecode_encode.lean](representationDecode_encode.lean)**

@import "representationDecode_encode.lean"

**[DataTypesAsLattices/Closures/representationEncode_fixed.lean](representationEncode_fixed.lean)**

@import "representationEncode_fixed.lean"

**[DataTypesAsLattices/Closures/representationOrderIso.lean](representationOrderIso.lean)**

@import "representationOrderIso.lean"

**[DataTypesAsLattices/Closures/retractBasis_eq_compactFixedBelow.lean](retractBasis_eq_compactFixedBelow.lean)**

@import "retractBasis_eq_compactFixedBelow.lean"

**[DataTypesAsLattices/Closures/fixed_eq_sSup_compacts.lean](fixed_eq_sSup_compacts.lean)**

@import "fixed_eq_sSup_compacts.lean"

**[DataTypesAsLattices/Closures/closureRangeCountablyAlgebraic.lean](closureRangeCountablyAlgebraic.lean)**

@import "closureRangeCountablyAlgebraic.lean"

**[DataTypesAsLattices/Closures/selfArrowStep.lean](selfArrowStep.lean)**

@import "selfArrowStep.lean"

**[DataTypesAsLattices/Closures/dEq.lean](dEq.lean)**

@import "dEq.lean"

**[DataTypesAsLattices/Closures/selfArrowStep_isScottContinuous.lean](selfArrowStep_isScottContinuous.lean)**

@import "selfArrowStep_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/eq_5_25.lean](eq_5_25.lean)**

@import "eq_5_25.lean"

**[DataTypesAsLattices/Closures/eq_5_25_arrow.lean](eq_5_25_arrow.lean)**

@import "eq_5_25_arrow.lean"

**[DataTypesAsLattices/Closures/squareFst.lean](squareFst.lean)**

@import "squareFst.lean"

**[DataTypesAsLattices/Closures/squareFst_bot.lean](squareFst_bot.lean)**

@import "squareFst_bot.lean"

**[DataTypesAsLattices/Closures/squareFst_isScottContinuous.lean](squareFst_isScottContinuous.lean)**

@import "squareFst_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/squareFst_top.lean](squareFst_top.lean)**

@import "squareFst_top.lean"

**[DataTypesAsLattices/Closures/squarePair.lean](squarePair.lean)**

@import "squarePair.lean"

**[DataTypesAsLattices/Closures/squarePair_bot_bot.lean](squarePair_bot_bot.lean)**

@import "squarePair_bot_bot.lean"

**[DataTypesAsLattices/Closures/squarePair_inj.lean](squarePair_inj.lean)**

@import "squarePair_inj.lean"

**[DataTypesAsLattices/Closures/squarePair_isScottContinuous_left.lean](squarePair_isScottContinuous_left.lean)**

@import "squarePair_isScottContinuous_left.lean"

**[DataTypesAsLattices/Closures/squarePair_isScottContinuous_right.lean](squarePair_isScottContinuous_right.lean)**

@import "squarePair_isScottContinuous_right.lean"

**[DataTypesAsLattices/Closures/squarePair_mono.lean](squarePair_mono.lean)**

@import "squarePair_mono.lean"

**[DataTypesAsLattices/Closures/Icomb_subset_boxTensor.lean](Icomb_subset_boxTensor.lean)**

@import "Icomb_subset_boxTensor.lean"

**[DataTypesAsLattices/Closures/squareSnd.lean](squareSnd.lean)**

@import "squareSnd.lean"

**[DataTypesAsLattices/Closures/boxPlus.lean](boxPlus.lean)**

@import "boxPlus.lean"

**[DataTypesAsLattices/Closures/boxTensor.lean](boxTensor.lean)**

@import "boxTensor.lean"

**[DataTypesAsLattices/Closures/squareSnd_bot.lean](squareSnd_bot.lean)**

@import "squareSnd_bot.lean"

**[DataTypesAsLattices/Closures/squareSnd_isScottContinuous.lean](squareSnd_isScottContinuous.lean)**

@import "squareSnd_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/boxTensor_app.lean](boxTensor_app.lean)**

@import "boxTensor_app.lean"

**[DataTypesAsLattices/Closures/boxTensor_isRetract.lean](boxTensor_isRetract.lean)**

@import "boxTensor_isRetract.lean"

**[DataTypesAsLattices/Closures/squareSnd_top.lean](squareSnd_top.lean)**

@import "squareSnd_top.lean"

**[DataTypesAsLattices/Closures/topElem_ne_botElem.lean](topElem_ne_botElem.lean)**

@import "topElem_ne_botElem.lean"

**[DataTypesAsLattices/Closures/typed_of_boxTensor.lean](typed_of_boxTensor.lean)**

@import "typed_of_boxTensor.lean"

**[DataTypesAsLattices/Closures/typed_squarePair_boxTensor.lean](typed_squarePair_boxTensor.lean)**

@import "typed_squarePair_boxTensor.lean"

**[DataTypesAsLattices/Closures/union_botElem.lean](union_botElem.lean)**

@import "union_botElem.lean"

**[DataTypesAsLattices/Closures/union_left_isScottContinuous.lean](union_left_isScottContinuous.lean)**

@import "union_left_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/union_const_left_isScottContinuous.lean](union_const_left_isScottContinuous.lean)**

@import "union_const_left_isScottContinuous.lean"












**[DataTypesAsLattices/Closures/boxShift_map_isScottContinuous.lean](boxShift_map_isScottContinuous.lean)**

@import "boxShift_map_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/boxShift_app.lean](boxShift_app.lean)**

@import "boxShift_app.lean"

**[DataTypesAsLattices/Closures/boxShift_expansive.lean](boxShift_expansive.lean)**

@import "boxShift_expansive.lean"

**[DataTypesAsLattices/Closures/Icomb_subset_boxShift.lean](Icomb_subset_boxShift.lean)**

@import "Icomb_subset_boxShift.lean"


**[DataTypesAsLattices/Closures/Icomb_subset_boxPlus.lean](Icomb_subset_boxPlus.lean)**

@import "Icomb_subset_boxPlus.lean"

**[DataTypesAsLattices/Closures/boxShift_isRetract.lean](boxShift_isRetract.lean)**

@import "boxShift_isRetract.lean"

**[DataTypesAsLattices/Closures/boxShift_isClosure.lean](boxShift_isClosure.lean)**

@import "boxShift_isClosure.lean"

**[DataTypesAsLattices/Closures/union_right_isScottContinuous.lean](union_right_isScottContinuous.lean)**

@import "union_right_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/Vstep_isScottContinuous.lean](Vstep_isScottContinuous.lean)**

@import "Vstep_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/eq_5_14.lean](eq_5_14.lean)**

@import "eq_5_14.lean"

**[DataTypesAsLattices/Closures/Vapply_left_isScottContinuous.lean](Vapply_left_isScottContinuous.lean)**

@import "Vapply_left_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/Vapply_right_isScottContinuous.lean](Vapply_right_isScottContinuous.lean)**

@import "Vapply_right_isScottContinuous.lean"

**[DataTypesAsLattices/Closures/Vapply_graph_isClosure.lean](Vapply_graph_isClosure.lean)**

@import "Vapply_graph_isClosure.lean"

**[DataTypesAsLattices/Closures/Vcomb_app.lean](Vcomb_app.lean)**

@import "Vcomb_app.lean"

**[DataTypesAsLattices/Closures/eq_5_21.lean](eq_5_21.lean)**

@import "eq_5_21.lean"

**[DataTypesAsLattices/Closures/Icomb_subset_Vcomb.lean](Icomb_subset_Vcomb.lean)**

@import "Icomb_subset_Vcomb.lean"

**[DataTypesAsLattices/Closures/typed_of_retract_Vcomb.lean](typed_of_retract_Vcomb.lean)**

@import "typed_of_retract_Vcomb.lean"

**[DataTypesAsLattices/Closures/zero_mem_boxShift_app.lean](zero_mem_boxShift_app.lean)**

@import "zero_mem_boxShift_app.lean"

**[DataTypesAsLattices/Closures/boxShift_app_ne_bot.lean](boxShift_app_ne_bot.lean)**

@import "boxShift_app_ne_bot.lean"






