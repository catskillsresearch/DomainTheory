# Embedding

- [Theorem 1.5](1976_Theorem_1_5.md)
- [Theorem 1.6](1976_Theorem_1_6.md)

**Dependencies.** Inside Embedding, each box is one Lean file. A box named as another folder in this chapter is that whole folder. A box named as another chapter is that whole chapter. The arrowhead points at the file or folder that imports, and the number is how many direct imports.

@import "Embedding.mermaid"

## AI: Human-English to AI-Lean

**[DataTypesAsLattices/Embedding/embed.lean](embed.lean)**

@import "embed.lean"

**[DataTypesAsLattices/Embedding/embed_continuous.lean](embed_continuous.lean)**

@import "embed_continuous.lean"

**[DataTypesAsLattices/Embedding/embed_inducing.lean](embed_inducing.lean)**

@import "embed_inducing.lean"

**[DataTypesAsLattices/Embedding/embed_injective.lean](embed_injective.lean)**

@import "embed_injective.lean"

**[DataTypesAsLattices/Embedding/extend.lean](extend.lean)**

@import "extend.lean"

**[DataTypesAsLattices/Embedding/mem_extend.lean](mem_extend.lean)**

@import "mem_extend.lean"

**[DataTypesAsLattices/Embedding/isOpen_extend_mem.lean](isOpen_extend_mem.lean)**

@import "isOpen_extend_mem.lean"

## AI: AI-Lean to AI-English

@import "embed.ai_lean_to_english" {code_block=false}

@import "embed_continuous.ai_lean_to_english" {code_block=false}

@import "embed_inducing.ai_lean_to_english" {code_block=false}

@import "embed_injective.ai_lean_to_english" {code_block=false}

@import "extend.ai_lean_to_english" {code_block=false}

@import "mem_extend.ai_lean_to_english" {code_block=false}

@import "isOpen_extend_mem.ai_lean_to_english" {code_block=false}
