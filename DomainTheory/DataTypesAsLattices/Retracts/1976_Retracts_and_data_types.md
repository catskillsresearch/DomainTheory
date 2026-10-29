# Retracts and data types

**Historical note.** A retract is an ordinary notion of topology. The use of computable retracts as data types, the operations on those retracts, and the recursive definitions by fixed-point equations are Scott's. A continuous lattice, in the sense of Scott (1972), has continuous meet and join, and as a space it is a $T_0$-space satisfying the extension theorem. The connection between lattices and fixed points was already known. The set of all retracts is a complete lattice by Theorem 4.1, and it is not itself a continuous lattice. Ershov solved that question after the body of the paper was written; Hosono and Sato (1975) found essentially the same argument independently. The argument is given with the ordering of retracts. The correspondence was Scott's introduction to Ershov's numeration theory. Applications to the semantics of flow diagrams are in Scott (1971), and were taken up by Goguen et al. (1975) and by Reynolds (1974).

**Dependencies.** Inside Retracts, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Retracts.mermaid"

@import "1976_Retracts_and_data_types.english" {code_block=false}

**[DataTypesAsLattices/Retracts/graph_ext.lean](graph_ext.lean)**

@import "graph_ext.lean"
**[DataTypesAsLattices/FixedLattices/DirectedSet.lean](../FixedLattices/DirectedSet.lean)**

@import "../FixedLattices/DirectedSet.lean"
**[DataTypesAsLattices/Retracts/predSet_ofNat_zero.lean](predSet_ofNat_zero.lean)**

@import "predSet_ofNat_zero.lean"
**[DataTypesAsLattices/FixedLattices/completeLatticeLE.lean](../FixedLattices/completeLatticeLE.lean)**

@import "../FixedLattices/completeLatticeLE.lean"
**[DataTypesAsLattices/FixedLattices/completeLatticePreorder.lean](../FixedLattices/completeLatticePreorder.lean)**

@import "../FixedLattices/completeLatticePreorder.lean"
**[DataTypesAsLattices/FixedLattices/completeLatticeSupSet.lean](../FixedLattices/completeLatticeSupSet.lean)**

@import "../FixedLattices/completeLatticeSupSet.lean"
**[DataTypesAsLattices/FixedLattices/WayBelow.lean](../FixedLattices/WayBelow.lean)**

@import "../FixedLattices/WayBelow.lean"
**[DataTypesAsLattices/Retracts/Fixpoints.lean](Fixpoints.lean)**

@import "Fixpoints.lean"
**[DataTypesAsLattices/Retracts/graph_const_bot.lean](graph_const_bot.lean)**

@import "graph_const_bot.lean"
**[DataTypesAsLattices/Retracts/predSet_eq_ofNat_of_no_zero.lean](predSet_eq_ofNat_of_no_zero.lean)**

@import "predSet_eq_ofNat_of_no_zero.lean"
**[DataTypesAsLattices/Retracts/vals.lean](vals.lean)**

@import "vals.lean"
**[DataTypesAsLattices/Retracts/DirectedSubset.lean](DirectedSubset.lean)**

@import "DirectedSubset.lean"
**[DataTypesAsLattices/Retracts/directed_finite_cover.lean](directed_finite_cover.lean)**

@import "directed_finite_cover.lean"
**[DataTypesAsLattices/Retracts/IsCompactSubset.lean](IsCompactSubset.lean)**

@import "IsCompactSubset.lean"
**[DataTypesAsLattices/Retracts/openR.lean](openR.lean)**

@import "openR.lean"
