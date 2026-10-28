# Embedding

- [Theorem 1.5](1976_Theorem_1_5.md)
- [Theorem 1.6](1976_Theorem_1_6.md)

**Dependencies.** Inside Embedding, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Embedding.mermaid"

**[DataTypesAsLattices/Embedding/extend.lean](DomainTheory/DataTypesAsLattices/Embedding/extend.lean)**

@import "extend.lean"
**[DataTypesAsLattices/Continuous/memOpen.lean](DomainTheory/DataTypesAsLattices/Continuous/memOpen.lean)**

@import "../Continuous/memOpen.lean"
**[DataTypesAsLattices/Continuous/Basic.lean](DomainTheory/DataTypesAsLattices/Continuous/Basic.lean)**

@import "../Continuous/Basic.lean"
**[DataTypesAsLattices/Embedding/embed.lean](DomainTheory/DataTypesAsLattices/Embedding/embed.lean)**

@import "embed.lean"
**[DataTypesAsLattices/Continuous/basicNhhd_more.lean](DomainTheory/DataTypesAsLattices/Continuous/basicNhhd_more.lean)**

@import "../Continuous/basicNhhd_more.lean"
**[DataTypesAsLattices/Continuous/exists_basicNhhd_subset_of_generateOpen.lean](DomainTheory/DataTypesAsLattices/Continuous/exists_basicNhhd_subset_of_generateOpen.lean)**

@import "../Continuous/exists_basicNhhd_subset_of_generateOpen.lean"
