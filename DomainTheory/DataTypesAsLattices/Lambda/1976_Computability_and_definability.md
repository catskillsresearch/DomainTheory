# Computability and definability

## Historical note

The language LAMBDA is Scott's. Plotkin and Rogers already used graphs, application, and conversion, and the combinators they had would have defined abstraction if anyone had asked; the abstraction operation is what this section supplies. The reduction theorem and the combinator theorem are the classical ones from combinatory logic. The first recursion theorem is classical as well. The argument that Curry's combinator $\mathbf{Y}$ is the least fixed point in this model is David Park's, from an unpublished note of 1970, and it is recorded with Theorem 2.5. The equation $\mathbf{Y}(u) = u(\mathbf{Y}(u))$ is the usual calculation from (2.8). Leastness uses the pairing $(n, m)$ and the finite sets $e_l$, and does not appeal to Theorem 1.4. The definition of computability and Theorem 2.6 identify the LAMBDA-definable functions with the enumeration operators.

**Dependency diagram.** Each box is one note that contains Lean. The arrowhead is on the note that imports. The number is how many direct imports. An arrow already implied by a longer path is left out.

@import "1976_Computability_and_definability.mermaid"

- [Meaning](1976_Meaning.md)
- [LAMBDA](1976_LAMBDA.md)
- [Theorem 2.1](1976_Theorem_2_1.md)
- [Theorem 2.2](1976_Theorem_2_2.md)
- [Theorem 2.3](1976_Theorem_2_3.md)
- [Theorem 2.4](1976_Theorem_2_4.md)
- [The combinator Y](1976_Combinator_Y.md)
- [Theorem 2.5](1976_Theorem_2_5.md)
- [The graph model](1976_Graph_model.md)
- [Elementary definitions](1976_Elementary_definitions.md)
- [Sequences](1976_Sequences.md)
- [Distributive functions](1976_Distributive_functions.md)
- [Primitive recursion](1976_Primitive_recursion.md)
- [Definition (computable)](1976_Definition_computable.md)
- [Computable functions](../Computability/1976_Computable_functions.md)
- [Definability](../Computability/1976_Definability.md)
- [Theorem 2.6](../Computability/1976_Theorem_2_6.md)
- [A law of Y](1976_Law_of_Y.md)
