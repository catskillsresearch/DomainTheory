# FixedPoint

- [Theorem 1.3](1976_Theorem_1_3.md)
- [Theorem 1.4](1976_Theorem_1_4.md)

**Dependencies.** Inside FixedPoint, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "FixedPoint.mermaid"

## AI: Human-English to AI-Lean

**[DataTypesAsLattices/FixedPoint/chain_mono.lean](chain_mono.lean)**

@import "chain_mono.lean"

**[DataTypesAsLattices/FixedPoint/exists_index_of_finset.lean](exists_index_of_finset.lean)**

@import "exists_index_of_finset.lean"

**[DataTypesAsLattices/FixedPoint/chain_lemma.lean](chain_lemma.lean)**

@import "chain_lemma.lean"

**[DataTypesAsLattices/FixedPoint/iterateBot.lean](iterateBot.lean)**

@import "iterateBot.lean"

**[DataTypesAsLattices/FixedPoint/fix.lean](fix.lean)**

@import "fix.lean"

**[DataTypesAsLattices/FixedPoint/iterateBot_mono.lean](iterateBot_mono.lean)**

@import "iterateBot_mono.lean"

## AI: AI-Lean to AI-English

@import "chain_mono.ai_lean_to_english" {code_block=false}

@import "exists_index_of_finset.ai_lean_to_english" {code_block=false}

@import "chain_lemma.ai_lean_to_english" {code_block=false}

@import "iterateBot.ai_lean_to_english" {code_block=false}

@import "fix.ai_lean_to_english" {code_block=false}

@import "iterateBot_mono.ai_lean_to_english" {code_block=false}
