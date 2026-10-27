# Exercise 8.26

**EXERCISE 8.26.** Discuss in more detail the "pay-off" for $U$, namely the translation of "untyped" $\lambda$-calculus into $U$ as shown by the equations at the end of the lecture after the proof of 8.9. In particular show how the whole of the **typed** $\lambda$-calculus can be retranslated back into $U$ with the aid of projections. (Hint: Whenever you want to write
$$
f : D_a \to D_b,
$$

<!-- page 150 -->

write instead

$$f = b \circ f \circ a,$$

where $a$, $b$ are finitary projections. Whenever you want to form a $\lambda$-abstraction

$$\lambda x^{D_a}.\,\sigma,$$

where $\sigma$ is of type $D_b$, instead form

$$\lambda x.\, b(\sigma'[a(x)/x]),$$

where $\sigma'$ is the further translation of $\sigma$ into untyped $\lambda$-calculus. Be sure to show that this result "has the right type" in the sense defined above.)

## Tip summary

The tip asserts β-soundness of the self-hosted encoding: `Uapply (Ulam f) x = f(x)`.

## Development

**[Exercise_8_26.lean](Exercise_8_26.lean)** — `exercise_8_26`

@import "Exercise_8_26.lean"
