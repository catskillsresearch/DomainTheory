# Theorem 2.3

By "model" here we of course understand the interpretation of the language where the semantics gives terms denotations in $\mathbf{P}\omega$ according to the stated definition. Through this interpretation, more properly speaking, $\mathbf{P}\omega$ becomes a model for the axioms $(\alpha)$, $(\beta)$, $(\xi)$. Two well-known results of the calculus of $\lambda$-conversion allow the reduction of functions of several variables to those of *one*, and the reduction of all the primitives to *combinators* (constants)—all this with the aid of the binary operation of application.

**THEOREM 2.3** (The reduction theorem). *Any continuous function of $k$-variables can be written as*

$$f(x_0, x_1, \cdots, x_{k-1}) = u(x_0)(x_1) \cdots (x_{k-1}),$$

*where $u$ is a suitably chosen element of $\mathbf{P}\omega$.*

**Lean 4**

- [DataTypesAsLattices/Lambda/theorem_2_3.lean](theorem_2_3.lean)
- [DataTypesAsLattices/Lambda/theorem_2_3_binary.lean](theorem_2_3_binary.lean)
- [DataTypesAsLattices/Lambda/theorem_2_3_ternary.lean](theorem_2_3_ternary.lean)
- [DataTypesAsLattices/Lambda/theorem_2_3_unary.lean](theorem_2_3_unary.lean)
