# Closure operations and algebraic lattices

**Historical note.** Algebraic lattices and closure operations predate the paper: Grätzer (1968) for the lattices, Tarski (1930) for the closures. Per Martin-Löf and Peter Hancock suggested that the continuous closures form a universe, and the construction of $\mathbf{V}$ is essentially theirs. The limit theorem is Scott's.

**Dependencies.** Inside Closures, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Closures.mermaid"

@import "1976_Closure_operations_and_algebraic_lattices.english" {code_block=false}

**[DataTypesAsLattices/Closures/Isolated.lean](DomainTheory/DataTypesAsLattices/Closures/Isolated.lean)**

@import "Isolated.lean"
**[DataTypesAsLattices/Closures/directed_finite_cover_subset.lean](DomainTheory/DataTypesAsLattices/Closures/directed_finite_cover_subset.lean)**

@import "directed_finite_cover_subset.lean"
**[DataTypesAsLattices/Closures/squarePair.lean](DomainTheory/DataTypesAsLattices/Closures/squarePair.lean)**

@import "squarePair.lean"
**[DataTypesAsLattices/FixedLattices/IsCompact.lean](DomainTheory/DataTypesAsLattices/FixedLattices/IsCompact.lean)**

@import "../FixedLattices/IsCompact.lean"
**[DataTypesAsLattices/FixedLattices/CountablyAlgebraic.lean](DomainTheory/DataTypesAsLattices/FixedLattices/CountablyAlgebraic.lean)**

@import "../FixedLattices/CountablyAlgebraic.lean"
**[DataTypesAsLattices/FixedLattices/finiteBasisSups.lean](DomainTheory/DataTypesAsLattices/FixedLattices/finiteBasisSups.lean)**

@import "../FixedLattices/finiteBasisSups.lean"
**[DataTypesAsLattices/FixedLattices/ContinuousBasis.lean](DomainTheory/DataTypesAsLattices/FixedLattices/ContinuousBasis.lean)**

@import "../FixedLattices/ContinuousBasis.lean"
**[DataTypesAsLattices/FixedLattices/finiteBasisSups_directed.lean](DomainTheory/DataTypesAsLattices/FixedLattices/finiteBasisSups_directed.lean)**

@import "../FixedLattices/finiteBasisSups_directed.lean"
**[DataTypesAsLattices/FixedLattices/sSup_finiteBasisSups.lean](DomainTheory/DataTypesAsLattices/FixedLattices/sSup_finiteBasisSups.lean)**

@import "../FixedLattices/sSup_finiteBasisSups.lean"
**[DataTypesAsLattices/FixedLattices/CountablyAlgebraicu2ecompact_finite_support.lean](DomainTheory/DataTypesAsLattices/FixedLattices/CountablyAlgebraicu2ecompact_finite_support.lean)**

@import "../FixedLattices/CountablyAlgebraicu2ecompact_finite_support.lean"
**[DataTypesAsLattices/Closures/representationEncode.lean](DomainTheory/DataTypesAsLattices/Closures/representationEncode.lean)**

@import "representationEncode.lean"
**[DataTypesAsLattices/Closures/representationDecode.lean](DomainTheory/DataTypesAsLattices/Closures/representationDecode.lean)**

@import "representationDecode.lean"
**[DataTypesAsLattices/Closures/exists_mem_of_ne_bot.lean](DomainTheory/DataTypesAsLattices/Closures/exists_mem_of_ne_bot.lean)**

@import "exists_mem_of_ne_bot.lean"
**[DataTypesAsLattices/Closures/predSet_succSet.lean](DomainTheory/DataTypesAsLattices/Closures/predSet_succSet.lean)**

@import "predSet_succSet.lean"
**[DataTypesAsLattices/Closures/predSet_union.lean](DomainTheory/DataTypesAsLattices/Closures/predSet_union.lean)**

@import "predSet_union.lean"
**[DataTypesAsLattices/Closures/topElem_ne_botElem.lean](DomainTheory/DataTypesAsLattices/Closures/topElem_ne_botElem.lean)**

@import "topElem_ne_botElem.lean"
**[DataTypesAsLattices/Closures/union_botElem.lean](DomainTheory/DataTypesAsLattices/Closures/union_botElem.lean)**

@import "union_botElem.lean"
**[DataTypesAsLattices/Closures/botElem_union.lean](DomainTheory/DataTypesAsLattices/Closures/botElem_union.lean)**

@import "botElem_union.lean"
