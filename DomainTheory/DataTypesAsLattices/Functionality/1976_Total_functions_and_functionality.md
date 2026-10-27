# Total functions and functionality

## Historical note

Functionality had long been studied in combinatory logic. Hindley, Lercher, and Seldin (1972) is the introduction Scott used. This section is his reading of that theory in $\mathbf{P}\omega$. The connection with the functional interpretation of intuitionistic logic goes back to Curry and Kleene, and Theorem 7.3 is the standard result of that interpretation. Theorem 7.4, that the obvious typing characterizes the iterators, is due to Gordon Plotkin.

**Dependencies.** Inside Functionality, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Functionality.mermaid"

@import "1976_Total_functions_and_functionality.english" {code_block=false}

**[DataTypesAsLattices/Functionality/Hcomb.lean](DomainTheory/DataTypesAsLattices/Functionality/Hcomb.lean)**

@import "Hcomb.lean"
**[DataTypesAsLattices/Functionality/Hcomb_more.lean](DomainTheory/DataTypesAsLattices/Functionality/Hcomb_more.lean)**

@import "Hcomb_more.lean"
**[DataTypesAsLattices/Functionality/Z.lean](DomainTheory/DataTypesAsLattices/Functionality/Z.lean)**

@import "Z.lean"
**[DataTypesAsLattices/Functionality/Zcomb.lean](DomainTheory/DataTypesAsLattices/Functionality/Zcomb.lean)**

@import "Zcomb.lean"
**[DataTypesAsLattices/Functionality/arrowR_diag_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/arrowR_diag_isScottContinuous.lean)**

@import "arrowR_diag_isScottContinuous.lean"
**[DataTypesAsLattices/Functionality/sigmaJ.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ.lean)**

@import "sigmaJ.lean"
**[DataTypesAsLattices/Functionality/finite_sigma_plain_app.lean](DomainTheory/DataTypesAsLattices/Functionality/finite_sigma_plain_app.lean)**

@import "finite_sigma_plain_app.lean"
**[DataTypesAsLattices/Functionality/eq_7_18_ne.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_7_18_ne.lean)**

@import "eq_7_18_ne.lean"
**[DataTypesAsLattices/Functionality/eq_7_18_eq.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_7_18_eq.lean)**

@import "eq_7_18_eq.lean"
**[DataTypesAsLattices/Functionality/finite_sigma_union_app.lean](DomainTheory/DataTypesAsLattices/Functionality/finite_sigma_union_app.lean)**

@import "finite_sigma_union_app.lean"
**[DataTypesAsLattices/Functionality/sumMed.lean](DomainTheory/DataTypesAsLattices/Functionality/sumMed.lean)**

@import "sumMed.lean"
**[DataTypesAsLattices/Functionality/tagInj_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tagInj_isScottContinuous.lean)**

@import "tagInj_isScottContinuous.lean"
