# Exercise 5.12

**EXERCISE 5.12.** On any domain $D$ introduce (as a least fixed point) a combinator

$$
\mathrm{while} : (D \to T) \times (D \to D) \to (D \to D)
$$

by the recursion

$$
\mathrm{while}(p, f)(x) = \mathrm{cond}(p(x), \mathrm{while}(p, f)(f(x)), x).
$$

Prove that

$$
\mathrm{while}(p, \mathrm{while}(p, f)) = \mathrm{while}(p, f).
$$

Show how $\mathrm{while}$ could have been used to obtain the least number operator mentioned in the proof of 5.6. Generalize the idea to define a combinator

$$
\mathrm{find} : D^\infty \times (D \to T) \to D
$$

with the meaning "find the first term of the sequence (if any) which satisfies the given precicate."

**[Exercise_5_12.lean](Exercise_5_12.lean)**

@import "Exercise_5_12.lean"
