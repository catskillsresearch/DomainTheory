# Subsets and their classification

## Historical note

The classification of these subsets by notions from descriptive set theory, and the connection with Wadge reducibility, are in the work of Adrian Tang. The normal forms for the classes, such as Table 3, are Scott's.

**Dependencies.** Inside Classification, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Classification.mermaid"

@import "1976_Subsets_and_their_classification.english" {code_block=false}

**[DataTypesAsLattices/Classification/IsBooleanOpen.lean](IsBooleanOpen.lean)**

@import "IsBooleanOpen.lean"

**[DataTypesAsLattices/Classification/BooleanMemE.lean](BooleanMemE.lean)**

@import "BooleanMemE.lean"

**[DataTypesAsLattices/Classification/IsBdelta.lean](IsBdelta.lean)**

@import "IsBdelta.lean"

**[DataTypesAsLattices/Classification/IsFcapG.lean](IsFcapG.lean)**

@import "IsFcapG.lean"

**[DataTypesAsLattices/Classification/Pi11.lean](Pi11.lean)**

@import "Pi11.lean"

**[DataTypesAsLattices/Classification/IsScottGdelta.lean](IsScottGdelta.lean)**

@import "IsScottGdelta.lean"

**[DataTypesAsLattices/Classification/IsFcapGdelta.lean](IsFcapGdelta.lean)**

@import "IsFcapGdelta.lean"

**[DataTypesAsLattices/Classification/IsSigma11.lean](IsSigma11.lean)**

@import "IsSigma11.lean"

**[DataTypesAsLattices/Classification/ThreeValued.lean](ThreeValued.lean)**

@import "ThreeValued.lean"

**[DataTypesAsLattices/Classification/ScottB.lean](ScottB.lean)**

@import "ScottB.lean"

**[DataTypesAsLattices/Classification/ScottF.lean](ScottF.lean)**

@import "ScottF.lean"

**[DataTypesAsLattices/Classification/ScottG.lean](ScottG.lean)**

@import "ScottG.lean"

**[DataTypesAsLattices/Classification/charOpen.lean](charOpen.lean)**

@import "charOpen.lean"

**[DataTypesAsLattices/Classification/charTop.lean](charTop.lean)**

@import "charTop.lean"

**[DataTypesAsLattices/Classification/closedToZero.lean](closedToZero.lean)**

@import "closedToZero.lean"

**[DataTypesAsLattices/Classification/evenPart.lean](evenPart.lean)**

@import "evenPart.lean"

**[DataTypesAsLattices/Classification/fcapGdeltaPack.lean](fcapGdeltaPack.lean)**

@import "fcapGdeltaPack.lean"

**[DataTypesAsLattices/Classification/oddEvenPack.lean](oddEvenPack.lean)**

@import "oddEvenPack.lean"

**[DataTypesAsLattices/Classification/oddPart.lean](oddPart.lean)**

@import "oddPart.lean"

**[DataTypesAsLattices/Classification/pairIndexed.lean](pairIndexed.lean)**

@import "pairIndexed.lean"

**[DataTypesAsLattices/Classification/typicalBdelta.lean](typicalBdelta.lean)**

@import "typicalBdelta.lean"

**[DataTypesAsLattices/Classification/typicalF.lean](typicalF.lean)**

@import "typicalF.lean"

**[DataTypesAsLattices/Classification/typicalFcapG.lean](typicalFcapG.lean)**

@import "typicalFcapG.lean"

**[DataTypesAsLattices/Classification/typicalFcapGdelta.lean](typicalFcapGdelta.lean)**

@import "typicalFcapGdelta.lean"

**[DataTypesAsLattices/Classification/typicalG.lean](typicalG.lean)**

@import "typicalG.lean"

**[DataTypesAsLattices/Classification/typicalGdelta.lean](typicalGdelta.lean)**

@import "typicalGdelta.lean"

**[DataTypesAsLattices/Classification/typicalPi11.lean](typicalPi11.lean)**

@import "typicalPi11.lean"

**[DataTypesAsLattices/Classification/typicalSigma11.lean](typicalSigma11.lean)**

@import "typicalSigma11.lean"

**[DataTypesAsLattices/Classification/uvU.lean](uvU.lean)**

@import "uvU.lean"

**[DataTypesAsLattices/Classification/uvV.lean](uvV.lean)**

@import "uvV.lean"

**[DataTypesAsLattices/Classification/zeroPrime.lean](zeroPrime.lean)**

@import "zeroPrime.lean"

**[DataTypesAsLattices/Classification/Basic.lean](Basic.lean)**

@import "Basic.lean"

**[DataTypesAsLattices/Classification/fcapGdeltaPack_isScottContinuous.lean](fcapGdeltaPack_isScottContinuous.lean)**

@import "fcapGdeltaPack_isScottContinuous.lean"

**[DataTypesAsLattices/Classification/isBdelta_inter.lean](isBdelta_inter.lean)**

@import "isBdelta_inter.lean"

**[DataTypesAsLattices/Classification/isBdelta_union.lean](isBdelta_union.lean)**

@import "isBdelta_union.lean"

**[DataTypesAsLattices/Classification/oddEvenPack_eq_zero.lean](oddEvenPack_eq_zero.lean)**

@import "oddEvenPack_eq_zero.lean"

**[DataTypesAsLattices/Classification/pairIndexed_eq_top.lean](pairIndexed_eq_top.lean)**

@import "pairIndexed_eq_top.lean"

**[DataTypesAsLattices/Classification/typicalBdelta_isBdelta.lean](typicalBdelta_isBdelta.lean)**

@import "typicalBdelta_isBdelta.lean"

**[DataTypesAsLattices/Classification/typicalGdelta_eq.lean](typicalGdelta_eq.lean)**

@import "typicalGdelta_eq.lean"

**[DataTypesAsLattices/Classification/typicalPi11_isPi11.lean](typicalPi11_isPi11.lean)**

@import "typicalPi11_isPi11.lean"

**[DataTypesAsLattices/Classification/typicalPi11_universal.lean](typicalPi11_universal.lean)**

@import "typicalPi11_universal.lean"

**[DataTypesAsLattices/Classification/typicalSigma11_isSigma11.lean](typicalSigma11_isSigma11.lean)**

@import "typicalSigma11_isSigma11.lean"

**[DataTypesAsLattices/Classification/typicalSigma11_universal.lean](typicalSigma11_universal.lean)**

@import "typicalSigma11_universal.lean"

**[DataTypesAsLattices/Classification/zero_not_mem_succSet_top.lean](zero_not_mem_succSet_top.lean)**

@import "zero_not_mem_succSet_top.lean"

**[DataTypesAsLattices/Classification/fcapGdeltaPack_eq.lean](fcapGdeltaPack_eq.lean)**

@import "fcapGdeltaPack_eq.lean"

