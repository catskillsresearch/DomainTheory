# Retracts and data types

## Historical note

A retract is an ordinary notion of topology. The use of computable retracts as data types, the operations on those retracts, and the recursive definitions by fixed-point equations are Scott's. A continuous lattice, in the sense of Scott (1972), has continuous meet and join, and as a space it is a $T_0$-space satisfying the extension theorem. The connection between lattices and fixed points was already known. The set of all retracts is a complete lattice by Theorem 4.1, and it is not itself a continuous lattice. Ershov solved that question after the body of the paper was written; Hosono and Sato (1975) found essentially the same argument independently. The argument is given with the ordering of retracts. The correspondence was Scott's introduction to Ershov's numeration theory. Applications to the semantics of flow diagrams are in Scott (1971), and were taken up by Goguen et al. (1975) and by Reynolds (1974).

**Dependencies.** Inside Retracts, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Retracts.mermaid"

@import "1976_Retracts_and_data_types.english" {code_block=false}

**[DataTypesAsLattices/FixedLattices/DirectedSet.lean](../FixedLattices/DirectedSet.lean)**

@import "../FixedLattices/DirectedSet.lean"

**[DataTypesAsLattices/Retracts/Icomb.lean](Icomb.lean)**

@import "Icomb.lean"
@import "Icomb.lean"

**[DataTypesAsLattices/Retracts/Icomb_app.lean](Icomb_app.lean)**

**[DataTypesAsLattices/Retracts/Icomb_isRetract.lean](Icomb_isRetract.lean)**

**[DataTypesAsLattices/Retracts/DirectedSubset.lean](DirectedSubset.lean)**

@import "DirectedSubset.lean"

**[DataTypesAsLattices/Retracts/boolR_app.lean](boolR_app.lean)**

**[DataTypesAsLattices/Retracts/comp.lean](comp.lean)**

@import "comp.lean"

**[DataTypesAsLattices/Retracts/arrowR.lean](arrowR.lean)**

@import "arrowR.lean"
@import "arrowR.lean"

**[DataTypesAsLattices/Retracts/arrowR_map_isScottContinuous.lean](arrowR_map_isScottContinuous.lean)**

**[DataTypesAsLattices/Retracts/arrowR_app.lean](arrowR_app.lean)**

**[DataTypesAsLattices/Retracts/arrowR_isStrict.lean](arrowR_isStrict.lean)**

**[DataTypesAsLattices/Retracts/dcondSet_bool_idem.lean](dcondSet_bool_idem.lean)**

@import "dcondSet_bool_idem.lean"

**[DataTypesAsLattices/Retracts/gfpBelow_isGLB.lean](gfpBelow_isGLB.lean)**

**[DataTypesAsLattices/Retracts/gfpBelow_le.lean](gfpBelow_le.lean)**

**[DataTypesAsLattices/Retracts/gfpBelow_postfixed.lean](gfpBelow_postfixed.lean)**

**[DataTypesAsLattices/Retracts/gfpBelow_fixed_inter.lean](gfpBelow_fixed_inter.lean)**

**[DataTypesAsLattices/Retracts/gfpBelow_subset.lean](gfpBelow_subset.lean)**

**[DataTypesAsLattices/Retracts/graph_ext.lean](graph_ext.lean)**

@import "graph_ext.lean"

**[DataTypesAsLattices/Retracts/boolR_isRetract.lean](boolR_isRetract.lean)**

**[DataTypesAsLattices/Retracts/eq_4_11.lean](eq_4_11.lean)**

@import "eq_4_11.lean"

**[DataTypesAsLattices/Retracts/arrowR_retractLe.lean](arrowR_retractLe.lean)**

**[DataTypesAsLattices/Retracts/funRetract.lean](funRetract.lean)**

@import "funRetract.lean"

**[DataTypesAsLattices/Retracts/intF_isScottContinuous.lean](intF_isScottContinuous.lean)**

**[DataTypesAsLattices/Retracts/intF_map_isScottContinuous.lean](intF_map_isScottContinuous.lean)**

**[DataTypesAsLattices/Retracts/intF_app.lean](intF_app.lean)**

**[DataTypesAsLattices/Retracts/intR_eq_intF.lean](intR_eq_intF.lean)**

**[DataTypesAsLattices/Retracts/intR_app.lean](intR_app.lean)**

**[DataTypesAsLattices/Retracts/intR_bot.lean](intR_bot.lean)**

**[DataTypesAsLattices/Retracts/intR_isGraph.lean](intR_isGraph.lean)**

**[DataTypesAsLattices/Retracts/intR_ofNat.lean](intR_ofNat.lean)**

**[DataTypesAsLattices/Retracts/inter_const_isScottContinuous.lean](inter_const_isScottContinuous.lean)**

@import "inter_const_isScottContinuous.lean"

**[DataTypesAsLattices/Retracts/iterateFrom_bot.lean](iterateFrom_bot.lean)**

**[DataTypesAsLattices/Retracts/iterateFrom_mono.lean](iterateFrom_mono.lean)**

**[DataTypesAsLattices/Retracts/lfpAbove.lean](lfpAbove.lean)**

@import "lfpAbove.lean"

**[DataTypesAsLattices/Retracts/lfpAbove_bot.lean](lfpAbove_bot.lean)**

**[DataTypesAsLattices/Retracts/lfpAbove_fixed.lean](lfpAbove_fixed.lean)**

**[DataTypesAsLattices/Retracts/lfpAbove_le_of_ub.lean](lfpAbove_le_of_ub.lean)**

**[DataTypesAsLattices/Retracts/lfpAbove_ub.lean](lfpAbove_ub.lean)**

**[DataTypesAsLattices/Retracts/pairSeq.lean](pairSeq.lean)**

@import "pairSeq.lean"

**[DataTypesAsLattices/Retracts/intR_top_of_nonsingleton.lean](intR_top_of_nonsingleton.lean)**

**[DataTypesAsLattices/Retracts/intR_top.lean](intR_top.lean)**

**[DataTypesAsLattices/Retracts/intR_idem.lean](intR_idem.lean)**

**[DataTypesAsLattices/Retracts/intR_isRetract.lean](intR_isRetract.lean)**

**[DataTypesAsLattices/Retracts/predSet_ofNat_zero.lean](predSet_ofNat_zero.lean)**

@import "predSet_ofNat_zero.lean"

**[DataTypesAsLattices/Retracts/retractBasis_directed.lean](retractBasis_directed.lean)**

**[DataTypesAsLattices/Retracts/retractBasis_directedSubset.lean](retractBasis_directedSubset.lean)**

**[DataTypesAsLattices/Retracts/retractLe.lean](retractLe.lean)**

@import "retractLe.lean"

**[DataTypesAsLattices/Retracts/retractLe_refl.lean](retractLe_refl.lean)**

**[DataTypesAsLattices/Retracts/retractLe_trans.lean](retractLe_trans.lean)**

**[DataTypesAsLattices/Retracts/retract_interpolation.lean](retract_interpolation.lean)**

@import "retract_interpolation.lean"

**[DataTypesAsLattices/Retracts/retractBasis_sSup.lean](retractBasis_sSup.lean)**

**[DataTypesAsLattices/Retracts/retractBasis_sUnion.lean](retractBasis_sUnion.lean)**

**[DataTypesAsLattices/Retracts/retractBasis_wayBelow.lean](retractBasis_wayBelow.lean)**

**[DataTypesAsLattices/Retracts/sUnion_Fixpoints_le_image.lean](sUnion_Fixpoints_le_image.lean)**

@import "sUnion_Fixpoints_le_image.lean"

**[DataTypesAsLattices/Retracts/lfpAbove_mem.lean](lfpAbove_mem.lean)**

**[DataTypesAsLattices/Retracts/sndC.lean](sndC.lean)**

@import "sndC.lean"

**[DataTypesAsLattices/Retracts/typed_of_arrowR.lean](typed_of_arrowR.lean)**

**[DataTypesAsLattices/Retracts/arrowR_functor.lean](arrowR_functor.lean)**

**[DataTypesAsLattices/Retracts/typed.lean](typed.lean)**

@import "typed.lean"

