# Enumeration and degrees

## Historical note

Reduction to a few combinators is old in combinatory logic. The device special to this model is (3.1), which folds the arithmetical combinators into the one combinator $\mathbf{G}$. The Gödel numbering and the second recursion theorem are the standard constructions, written so that arithmetic and the type-free combinators share a notation, and the incompleteness theorem is the standard one in that notation. Theorem 3.5 is the argument of Myhill and Shepherdson (1955); Martin Hyland pointed out the connection. Theorem 3.6 restates enumeration degrees, as in Rogers (1967), Sasso (1975), and Gutteridge (1971). Scott notes that this area was underdeveloped beside the theory of Turing degrees. Semigroups of combinators had been discussed by Church and by Böhm, and Theorem 3.7 reads that discussion inside $\mathbf{RE} \cap \mathbf{FUN}$.

**Dependencies.** Inside Enumeration, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Enumeration.mermaid"

@import "1976_Enumeration_and_degrees.english" {code_block=false}

**[DataTypesAsLattices/Enumeration/Deg.lean](Deg.lean)**

@import "Deg.lean"
**[DataTypesAsLattices/Enumeration/Rcomb.lean](Rcomb.lean)**

@import "Rcomb.lean"
@import "Rcomb.lean"

**[DataTypesAsLattices/Enumeration/barPos.lean](barPos.lean)**

@import "barPos.lean"
**[DataTypesAsLattices/Enumeration/barComb.lean](barComb.lean)**

@import "barComb.lean"
@import "barComb.lean"

**[DataTypesAsLattices/Enumeration/Gbar.lean](Gbar.lean)**

@import "Gbar.lean"
