# Definition 6.13

## Human-English

**DEFINITION 6.13.** A functor $T$ is *monotone on domains* iff whenever $D \triangleleft E$, then not only do we have $T(D) \triangleleft T(E)$ but the projection pair $i, j$ of 6.12 is mapped to the same kind of projection pair $T(i), T(j)$. A monotone functor is *continuous on domains* iff whenever $E$ is a domain, then the mapping

$$
\lambda D.\, T(D) : \{D \mid D \triangleleft E\} \to \{D' \mid D' \triangleleft T(E)\}
$$

is approximable. $\square$

<!-- page 107 -->

We can now state an existence theorem that covers in fairly wide generality the examples of this lecture.

## AI: Human-English to AI-Lean

**[Definition_6_13.lean](Definition_6_13.lean)**

@import "Definition_6_13.lean"
