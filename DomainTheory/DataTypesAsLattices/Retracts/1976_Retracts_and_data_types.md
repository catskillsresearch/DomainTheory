# Retracts and data types

**Historical note.** A retract is an ordinary notion of topology. The use of computable retracts as data types, the operations on those retracts, and the recursive definitions by fixed-point equations are Scott's. A continuous lattice, in the sense of Scott (1972), has continuous meet and join, and as a space it is a $T_0$-space satisfying the extension theorem. The connection between lattices and fixed points was already known. The set of all retracts is a complete lattice by Theorem 4.1, and it is not itself a continuous lattice. Ershov solved that question after the body of the paper was written; Hosono and Sato (1975) found essentially the same argument independently. The argument is given with the ordering of retracts. The correspondence was Scott's introduction to Ershov's numeration theory. Applications to the semantics of flow diagrams are in Scott (1971), and were taken up by Goguen et al. (1975) and by Reynolds (1974).

**Dependencies.** Inside Retracts, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Retracts.mermaid"

@import "1976_Retracts_and_data_types.english" {code_block=false}

**[DataTypesAsLattices/FixedLattices/DirectedSet.lean](DomainTheory/DataTypesAsLattices/FixedLattices/DirectedSet.lean)**

@import "../FixedLattices/DirectedSet.lean"
**[DataTypesAsLattices/Retracts/Icomb.lean](DomainTheory/DataTypesAsLattices/Retracts/Icomb.lean)**

@import "Icomb.lean"
**[DataTypesAsLattices/Retracts/DirectedSubset.lean](DomainTheory/DataTypesAsLattices/Retracts/DirectedSubset.lean)**

@import "DirectedSubset.lean"
**[DataTypesAsLattices/Retracts/boolR.lean](DomainTheory/DataTypesAsLattices/Retracts/boolR.lean)**

@import "boolR.lean"
**[DataTypesAsLattices/Retracts/comp.lean](DomainTheory/DataTypesAsLattices/Retracts/comp.lean)**

@import "comp.lean"
**[DataTypesAsLattices/Retracts/arrowR.lean](DomainTheory/DataTypesAsLattices/Retracts/arrowR.lean)**

@import "arrowR.lean"
**[DataTypesAsLattices/Retracts/arrowR_more.lean](DomainTheory/DataTypesAsLattices/Retracts/arrowR_more.lean)**

@import "arrowR_more.lean"
**[DataTypesAsLattices/Retracts/dcondSet_bool_idem.lean](DomainTheory/DataTypesAsLattices/Retracts/dcondSet_bool_idem.lean)**

@import "dcondSet_bool_idem.lean"
**[DataTypesAsLattices/Retracts/gfpBelow.lean](DomainTheory/DataTypesAsLattices/Retracts/gfpBelow.lean)**

@import "gfpBelow.lean"
**[DataTypesAsLattices/Retracts/graph_ext.lean](DomainTheory/DataTypesAsLattices/Retracts/graph_ext.lean)**

@import "graph_ext.lean"
**[DataTypesAsLattices/Retracts/eq_4_11.lean](DomainTheory/DataTypesAsLattices/Retracts/eq_4_11.lean)**

@import "eq_4_11.lean"
**[DataTypesAsLattices/Retracts/funRetract.lean](DomainTheory/DataTypesAsLattices/Retracts/funRetract.lean)**

@import "funRetract.lean"
**[DataTypesAsLattices/Retracts/intF.lean](DomainTheory/DataTypesAsLattices/Retracts/intF.lean)**

@import "intF.lean"
**[DataTypesAsLattices/Retracts/intR.lean](DomainTheory/DataTypesAsLattices/Retracts/intR.lean)**

@import "intR.lean"
**[DataTypesAsLattices/Retracts/iterateFrom.lean](DomainTheory/DataTypesAsLattices/Retracts/iterateFrom.lean)**

@import "iterateFrom.lean"
**[DataTypesAsLattices/Retracts/lfpAbove.lean](DomainTheory/DataTypesAsLattices/Retracts/lfpAbove.lean)**

@import "lfpAbove.lean"
**[DataTypesAsLattices/Retracts/pairSeq.lean](DomainTheory/DataTypesAsLattices/Retracts/pairSeq.lean)**

@import "pairSeq.lean"
**[DataTypesAsLattices/Retracts/predSet_ofNat_zero.lean](DomainTheory/DataTypesAsLattices/Retracts/predSet_ofNat_zero.lean)**

@import "predSet_ofNat_zero.lean"
**[DataTypesAsLattices/Retracts/retractBasis.lean](DomainTheory/DataTypesAsLattices/Retracts/retractBasis.lean)**

@import "retractBasis.lean"
**[DataTypesAsLattices/Retracts/retractLe.lean](DomainTheory/DataTypesAsLattices/Retracts/retractLe.lean)**

@import "retractLe.lean"
**[DataTypesAsLattices/Retracts/retract_interpolation.lean](DomainTheory/DataTypesAsLattices/Retracts/retract_interpolation.lean)**

@import "retract_interpolation.lean"
**[DataTypesAsLattices/Retracts/sUnion_Fixpoints_le_image.lean](DomainTheory/DataTypesAsLattices/Retracts/sUnion_Fixpoints_le_image.lean)**

@import "sUnion_Fixpoints_le_image.lean"
**[DataTypesAsLattices/Retracts/sndC.lean](DomainTheory/DataTypesAsLattices/Retracts/sndC.lean)**

@import "sndC.lean"
**[DataTypesAsLattices/Retracts/typed_more.lean](DomainTheory/DataTypesAsLattices/Retracts/typed_more.lean)**

@import "typed_more.lean"
**[DataTypesAsLattices/Retracts/typed.lean](DomainTheory/DataTypesAsLattices/Retracts/typed.lean)**

@import "typed.lean"
