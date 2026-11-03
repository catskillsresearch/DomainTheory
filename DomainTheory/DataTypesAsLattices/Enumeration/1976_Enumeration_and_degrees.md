# Enumeration and degrees

**Historical note.** Reduction to a few combinators is old in combinatory logic. The device special to this model is (3.1), which folds the arithmetical combinators into the one combinator $\mathbf{G}$. The Gödel numbering and the second recursion theorem are the standard constructions, written so that arithmetic and the type-free combinators share a notation, and the incompleteness theorem is the standard one in that notation. Theorem 3.5 is the argument of Myhill and Shepherdson (1955); Martin Hyland pointed out the connection. Theorem 3.6 restates enumeration degrees, as in Rogers (1967), Sasso (1975), and Gutteridge (1971). Scott notes that this area was underdeveloped beside the theory of Turing degrees. Semigroups of combinators had been discussed by Church and by Böhm, and Theorem 3.7 reads that discussion inside $\mathbf{RE} \cap \mathbf{FUN}$.

**Dependencies.** Inside Enumeration, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Enumeration.mermaid"

@import "1976_Enumeration_and_degrees.english" {code_block=false}

- [Term avoidance (α)](1976_Avoids.md) ✓
- [Theorem 3.1](1976_Theorem_3_1.md)
- [Application](1976_Application.md)
- [Numerals](1976_Numerals.md)
- [Theorem 3.2](1976_Theorem_3_2.md)
- [Theorem 3.3](1976_Theorem_3_3.md)
- [Theorem 3.4](1976_Theorem_3_4.md)
- [Theorem 3.5](1976_Theorem_3_5.md)
- [Theorem 3.6](1976_Theorem_3_6.md)
- [Theorem 3.7](1976_Theorem_3_7.md)


**[DataTypesAsLattices/Enumeration/argNat.lean](argNat.lean)**

@import "argNat.lean"
**[DataTypesAsLattices/Enumeration/bitList.lean](bitList.lean)**

@import "bitList.lean"
**[DataTypesAsLattices/Enumeration/eq_3_10_apply.lean](eq_3_10_apply.lean)**

@import "eq_3_10_apply.lean"
**[DataTypesAsLattices/Enumeration/eq_3_8_apply.lean](eq_3_8_apply.lean)**

@import "eq_3_8_apply.lean"
**[DataTypesAsLattices/Enumeration/opNat.lean](opNat.lean)**

@import "opNat.lean"
**[DataTypesAsLattices/Enumeration/eq_3_5.lean](eq_3_5.lean)**

@import "eq_3_5.lean"
**[DataTypesAsLattices/Enumeration/secondRecSubst.lean](secondRecSubst.lean)**

@import "secondRecSubst.lean"
**[DataTypesAsLattices/Enumeration/exists_triangle_succ.lean](exists_triangle_succ.lean)**

@import "exists_triangle_succ.lean"
**[DataTypesAsLattices/Enumeration/unpairComp.lean](unpairComp.lean)**

@import "unpairComp.lean"
**[DataTypesAsLattices/Enumeration/unpairWRec.lean](unpairWRec.lean)**

@import "unpairWRec.lean"
**[DataTypesAsLattices/Enumeration/unpairW.lean](unpairW.lean)**

@import "unpairW.lean"
**[DataTypesAsLattices/Enumeration/valRank.lean](valRank.lean)**

@import "valRank.lean"
**[DataTypesAsLattices/Enumeration/Extensional.lean](Extensional.lean)**

@import "Extensional.lean"
**[DataTypesAsLattices/Enumeration/recNat.lean](recNat.lean)**

@import "recNat.lean"
**[DataTypesAsLattices/Enumeration/eq_3_9_apply.lean](eq_3_9_apply.lean)**

@import "eq_3_9_apply.lean"
**[DataTypesAsLattices/Enumeration/eq_3_6.lean](eq_3_6.lean)**

@import "eq_3_6.lean"
**[DataTypesAsLattices/Enumeration/e_subset_ofNat_iff.lean](e_subset_ofNat_iff.lean)**

@import "e_subset_ofNat_iff.lean"
