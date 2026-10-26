# Retracts and data types

## Historical note

A retract is an ordinary notion of topology. The use of computable retracts as data types, the operations on those retracts, and the recursive definitions by fixed-point equations are Scott's. A continuous lattice, in the sense of Scott (1972), has continuous meet and join, and as a space it is a $T_0$-space satisfying the extension theorem. The connection between lattices and fixed points was already known. The set of all retracts is a complete lattice by Theorem 4.1, and it is not itself a continuous lattice. Ershov solved that question after the body of the paper was written; Hosono and Sato (1975) found essentially the same argument independently. The argument is given with the ordering of retracts. The correspondence was Scott's introduction to Ershov's numeration theory. Applications to the semantics of flow diagrams are in Scott (1971), and were taken up by Goguen et al. (1975) and by Reynolds (1974).

**Dependencies.** Inside Retracts, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Retracts.mermaid"

@import "1976_Retracts_and_data_types.english" {code_block=false}

**[DataTypesAsLattices/FixedLattices/DirectedSet.lean](../FixedLattices/DirectedSet.lean)**

@import "../FixedLattices/DirectedSet.lean"

**[DataTypesAsLattices/FixedLattices/completeLatticeLE.lean](../FixedLattices/completeLatticeLE.lean)**

@import "../FixedLattices/completeLatticeLE.lean"

**[DataTypesAsLattices/FixedLattices/completeLatticePreorder.lean](../FixedLattices/completeLatticePreorder.lean)**

@import "../FixedLattices/completeLatticePreorder.lean"

**[DataTypesAsLattices/FixedLattices/completeLatticeSupSet.lean](../FixedLattices/completeLatticeSupSet.lean)**

@import "../FixedLattices/completeLatticeSupSet.lean"

**[DataTypesAsLattices/FixedLattices/WayBelow.lean](../FixedLattices/WayBelow.lean)**

@import "../FixedLattices/WayBelow.lean"

**[DataTypesAsLattices/FixedLattices/IsCompact.lean](../FixedLattices/IsCompact.lean)**

@import "../FixedLattices/IsCompact.lean"

**[DataTypesAsLattices/FixedLattices/CountablyAlgebraic.lean](../FixedLattices/CountablyAlgebraic.lean)**

@import "../FixedLattices/CountablyAlgebraic.lean"

**[DataTypesAsLattices/FixedLattices/ContinuousBasis.lean](../FixedLattices/ContinuousBasis.lean)**

@import "../FixedLattices/ContinuousBasis.lean"

**[DataTypesAsLattices/FixedLattices/finiteBasisSups.lean](../FixedLattices/finiteBasisSups.lean)**

@import "../FixedLattices/finiteBasisSups.lean"

**[DataTypesAsLattices/FixedLattices/finiteBasisSups_directed.lean](../FixedLattices/finiteBasisSups_directed.lean)**

@import "../FixedLattices/finiteBasisSups_directed.lean"

**[DataTypesAsLattices/FixedLattices/sSup_finiteBasisSups.lean](../FixedLattices/sSup_finiteBasisSups.lean)**

@import "../FixedLattices/sSup_finiteBasisSups.lean"

**[DataTypesAsLattices/FixedLattices/CountablyAlgebraicu2ecompact_finite_support.lean](../FixedLattices/CountablyAlgebraicu2ecompact_finite_support.lean)**

@import "../FixedLattices/CountablyAlgebraicu2ecompact_finite_support.lean"

**[DataTypesAsLattices/FixedLattices.lean](../FixedLattices.lean)**

@import "../FixedLattices.lean"

**[DataTypesAsLattices/Retracts/Fixpoints.lean](Fixpoints.lean)**

@import "Fixpoints.lean"

**[DataTypesAsLattices/Retracts/Icomb.lean](Icomb.lean)**

@import "Icomb.lean"

**[DataTypesAsLattices/Retracts/Icomb_app.lean](Icomb_app.lean)**

@import "Icomb_app.lean"

**[DataTypesAsLattices/Retracts/Icomb_isRetract.lean](Icomb_isRetract.lean)**

@import "Icomb_isRetract.lean"

**[DataTypesAsLattices/Retracts/DirectedSubset.lean](DirectedSubset.lean)**

@import "DirectedSubset.lean"

**[DataTypesAsLattices/Retracts/IsCompactSubset.lean](IsCompactSubset.lean)**

@import "IsCompactSubset.lean"

**[DataTypesAsLattices/Retracts/boolR_app.lean](boolR_app.lean)**

@import "boolR_app.lean"

**[DataTypesAsLattices/Retracts/comp.lean](comp.lean)**

@import "comp.lean"

**[DataTypesAsLattices/Retracts/Retract.lean](Retract.lean)**

@import "Retract.lean"

**[DataTypesAsLattices/Retracts/arrowR.lean](arrowR.lean)**

@import "arrowR.lean"

**[DataTypesAsLattices/Retracts/comp_app.lean](comp_app.lean)**

@import "comp_app.lean"

**[DataTypesAsLattices/Retracts/comp_isScottContinuous_right.lean](comp_isScottContinuous_right.lean)**

@import "comp_isScottContinuous_right.lean"

**[DataTypesAsLattices/Retracts/comp_right_const.lean](comp_right_const.lean)**

@import "comp_right_const.lean"

**[DataTypesAsLattices/Retracts/arrowR_map_isScottContinuous.lean](arrowR_map_isScottContinuous.lean)**

@import "arrowR_map_isScottContinuous.lean"

**[DataTypesAsLattices/Retracts/arrowR_app.lean](arrowR_app.lean)**

@import "arrowR_app.lean"

**[DataTypesAsLattices/Retracts/arrowR_isStrict.lean](arrowR_isStrict.lean)**

@import "arrowR_isStrict.lean"

**[DataTypesAsLattices/Retracts/dcondSet_bool_idem.lean](dcondSet_bool_idem.lean)**

@import "dcondSet_bool_idem.lean"

**[DataTypesAsLattices/Retracts/dcondSet_same_ofNat.lean](dcondSet_same_ofNat.lean)**

@import "dcondSet_same_ofNat.lean"

**[DataTypesAsLattices/Retracts/directed_finite_cover.lean](directed_finite_cover.lean)**

@import "directed_finite_cover.lean"

**[DataTypesAsLattices/Retracts/directed_sUnion_fixed.lean](directed_sUnion_fixed.lean)**

@import "directed_sUnion_fixed.lean"

**[DataTypesAsLattices/Retracts/eq_4_11.lean](eq_4_11.lean)**

@import "eq_4_11.lean"

**[DataTypesAsLattices/Retracts/fstC.lean](fstC.lean)**

@import "fstC.lean"

**[DataTypesAsLattices/Retracts/fstC_app.lean](fstC_app.lean)**

@import "fstC_app.lean"

**[DataTypesAsLattices/Retracts/funOf_fix_idem.lean](funOf_fix_idem.lean)**

@import "funOf_fix_idem.lean"

**[DataTypesAsLattices/Retracts/funRetract.lean](funRetract.lean)**

@import "funRetract.lean"

**[DataTypesAsLattices/Retracts/funRetract_app.lean](funRetract_app.lean)**

@import "funRetract_app.lean"

**[DataTypesAsLattices/Retracts/gfpBelow.lean](gfpBelow.lean)**

@import "gfpBelow.lean"

**[DataTypesAsLattices/Retracts/gfpBelow_isGLB.lean](gfpBelow_isGLB.lean)**

@import "gfpBelow_isGLB.lean"

**[DataTypesAsLattices/Retracts/gfpBelow_le.lean](gfpBelow_le.lean)**

@import "gfpBelow_le.lean"

**[DataTypesAsLattices/Retracts/gfpBelow_postfixed.lean](gfpBelow_postfixed.lean)**

@import "gfpBelow_postfixed.lean"

**[DataTypesAsLattices/Retracts/gfpBelow_fixed_inter.lean](gfpBelow_fixed_inter.lean)**

@import "gfpBelow_fixed_inter.lean"

**[DataTypesAsLattices/Retracts/gfpBelow_subset.lean](gfpBelow_subset.lean)**

@import "gfpBelow_subset.lean"

**[DataTypesAsLattices/Retracts/graph_ext.lean](graph_ext.lean)**

@import "graph_ext.lean"

**[DataTypesAsLattices/Retracts/boolR_isRetract.lean](boolR_isRetract.lean)**

@import "boolR_isRetract.lean"

**[DataTypesAsLattices/Retracts/eq_4_11_comp.lean](eq_4_11_comp.lean)**

@import "eq_4_11_comp.lean"

**[DataTypesAsLattices/Retracts/arrowR_retractLe.lean](arrowR_retractLe.lean)**

@import "arrowR_retractLe.lean"

**[DataTypesAsLattices/Retracts/funRetract_isRetract.lean](funRetract_isRetract.lean)**

@import "funRetract_isRetract.lean"

**[DataTypesAsLattices/Retracts/intF_isScottContinuous.lean](intF_isScottContinuous.lean)**

@import "intF_isScottContinuous.lean"

**[DataTypesAsLattices/Retracts/intF_map_isScottContinuous.lean](intF_map_isScottContinuous.lean)**

@import "intF_map_isScottContinuous.lean"

**[DataTypesAsLattices/Retracts/intF_app.lean](intF_app.lean)**

@import "intF_app.lean"

**[DataTypesAsLattices/Retracts/intR_eq_intF.lean](intR_eq_intF.lean)**

@import "intR_eq_intF.lean"

**[DataTypesAsLattices/Retracts/intR_app.lean](intR_app.lean)**

@import "intR_app.lean"

**[DataTypesAsLattices/Retracts/intR_bot.lean](intR_bot.lean)**

@import "intR_bot.lean"

**[DataTypesAsLattices/Retracts/intR_isGraph.lean](intR_isGraph.lean)**

@import "intR_isGraph.lean"

**[DataTypesAsLattices/Retracts/intR_ofNat.lean](intR_ofNat.lean)**

@import "intR_ofNat.lean"

**[DataTypesAsLattices/Retracts/inter_const_isScottContinuous.lean](inter_const_isScottContinuous.lean)**

@import "inter_const_isScottContinuous.lean"

**[DataTypesAsLattices/Retracts/iterateFrom.lean](iterateFrom.lean)**

@import "iterateFrom.lean"

**[DataTypesAsLattices/Retracts/iterateFrom_bot.lean](iterateFrom_bot.lean)**

@import "iterateFrom_bot.lean"

**[DataTypesAsLattices/Retracts/iterateFrom_mono.lean](iterateFrom_mono.lean)**

@import "iterateFrom_mono.lean"

**[DataTypesAsLattices/Retracts/lfpAbove.lean](lfpAbove.lean)**

@import "lfpAbove.lean"

**[DataTypesAsLattices/Retracts/lfpAbove_bot.lean](lfpAbove_bot.lean)**

@import "lfpAbove_bot.lean"

**[DataTypesAsLattices/Retracts/lfpAbove_fixed.lean](lfpAbove_fixed.lean)**

@import "lfpAbove_fixed.lean"

**[DataTypesAsLattices/Retracts/lfpAbove_le_of_ub.lean](lfpAbove_le_of_ub.lean)**

@import "lfpAbove_le_of_ub.lean"

**[DataTypesAsLattices/Retracts/lfpAbove_ub.lean](lfpAbove_ub.lean)**

@import "lfpAbove_ub.lean"

**[DataTypesAsLattices/Retracts/pairSeq.lean](pairSeq.lean)**

@import "pairSeq.lean"

**[DataTypesAsLattices/Retracts/plusR.lean](plusR.lean)**

@import "plusR.lean"

**[DataTypesAsLattices/Retracts/predSet_eq_ofNat_of_no_zero.lean](predSet_eq_ofNat_of_no_zero.lean)**

@import "predSet_eq_ofNat_of_no_zero.lean"

**[DataTypesAsLattices/Retracts/intR_top_of_nonsingleton.lean](intR_top_of_nonsingleton.lean)**

@import "intR_top_of_nonsingleton.lean"

**[DataTypesAsLattices/Retracts/intR_top.lean](intR_top.lean)**

@import "intR_top.lean"

**[DataTypesAsLattices/Retracts/intR_idem.lean](intR_idem.lean)**

@import "intR_idem.lean"

**[DataTypesAsLattices/Retracts/intR_isRetract.lean](intR_isRetract.lean)**

@import "intR_isRetract.lean"

**[DataTypesAsLattices/Retracts/predSet_ofNat_zero.lean](predSet_ofNat_zero.lean)**

@import "predSet_ofNat_zero.lean"

**[DataTypesAsLattices/Retracts/retractBasis_directed.lean](retractBasis_directed.lean)**

@import "retractBasis_directed.lean"

**[DataTypesAsLattices/Retracts/retractBasis_directedSubset.lean](retractBasis_directedSubset.lean)**

@import "retractBasis_directedSubset.lean"

**[DataTypesAsLattices/Retracts/retractLe.lean](retractLe.lean)**

@import "retractLe.lean"

**[DataTypesAsLattices/Retracts/retractLe_refl.lean](retractLe_refl.lean)**

@import "retractLe_refl.lean"

**[DataTypesAsLattices/Retracts/retractLe_trans.lean](retractLe_trans.lean)**

@import "retractLe_trans.lean"

**[DataTypesAsLattices/Retracts/retract_interpolation.lean](retract_interpolation.lean)**

@import "retract_interpolation.lean"

**[DataTypesAsLattices/Retracts/retract_isGraph.lean](retract_isGraph.lean)**

@import "retract_isGraph.lean"

**[DataTypesAsLattices/Retracts/iUnion_retract_isGraph.lean](iUnion_retract_isGraph.lean)**

@import "iUnion_retract_isGraph.lean"

**[DataTypesAsLattices/Retracts/sSup_fixed_eq_sUnion.lean](sSup_fixed_eq_sUnion.lean)**

@import "sSup_fixed_eq_sUnion.lean"

**[DataTypesAsLattices/Retracts/retractBasis_sSup.lean](retractBasis_sSup.lean)**

@import "retractBasis_sSup.lean"

**[DataTypesAsLattices/Retracts/retractBasis_sUnion.lean](retractBasis_sUnion.lean)**

@import "retractBasis_sUnion.lean"

**[DataTypesAsLattices/Retracts/retractBasis_wayBelow.lean](retractBasis_wayBelow.lean)**

@import "retractBasis_wayBelow.lean"

**[DataTypesAsLattices/Retracts/sUnion_Fixpoints_le_image.lean](sUnion_Fixpoints_le_image.lean)**

@import "sUnion_Fixpoints_le_image.lean"

**[DataTypesAsLattices/Retracts/lfpAbove_mem.lean](lfpAbove_mem.lean)**

@import "lfpAbove_mem.lean"

**[DataTypesAsLattices/Retracts/sndC.lean](sndC.lean)**

@import "sndC.lean"

**[DataTypesAsLattices/Retracts/sndC_app.lean](sndC_app.lean)**

@import "sndC_app.lean"

**[DataTypesAsLattices/Retracts/tensorR.lean](tensorR.lean)**

@import "tensorR.lean"

**[DataTypesAsLattices/Retracts/typed.lean](typed.lean)**

@import "typed.lean"

**[DataTypesAsLattices/Retracts/typed_of_arrowR.lean](typed_of_arrowR.lean)**

@import "typed_of_arrowR.lean"

**[DataTypesAsLattices/Retracts/arrowR_functor.lean](arrowR_functor.lean)**

@import "arrowR_functor.lean"

**[DataTypesAsLattices/Retracts/typed_arrowR_range.lean](typed_arrowR_range.lean)**

@import "typed_arrowR_range.lean"

**[DataTypesAsLattices/Retracts/typed_arrowR_restrict.lean](typed_arrowR_restrict.lean)**

@import "typed_arrowR_restrict.lean"

**[DataTypesAsLattices/Retracts/typed_comp.lean](typed_comp.lean)**

@import "typed_comp.lean"

**[DataTypesAsLattices/Retracts/vals.lean](vals.lean)**

@import "vals.lean"

**[DataTypesAsLattices/Retracts/vals_subset.lean](vals_subset.lean)**

@import "vals_subset.lean"

