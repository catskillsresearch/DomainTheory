# Exercise 5.16

**EXERCISE 5.16.** Return to the discussion of Example 4.4 and the construction of the domain of finite and infinite binary sequences. Give a fixed-point definition of $\mathrm{neg} : C \to C$, where

$$
\mathrm{neg}(0x) = 1\,\mathrm{neg}(x); \qquad \mathrm{neg}(1x) = 0\,\mathrm{neg}(x).
$$

Prove that $\mathrm{neg}(\mathrm{neg}(x)) = x$ for all $x \in |C|$. Also define $\mathrm{merge} : C \times C \to C$, where for $\epsilon, \delta \in \{0, 1\}$ we have:

$$
\mathrm{merge}(\epsilon x, \delta y) = \epsilon\,\delta\,\mathrm{merge}(x, y).
$$

(Note: There may be a little trouble with $\mathrm{merge}(x, y)$ when $x$ is finite and total and $y$ is infinite—you have to decide what you want in e.g. $\mathrm{merge}(\Lambda, y)$.) Prove that

$$
\mathrm{merge}(x, x) = d(x),
$$

in the notation of 4.4. Consider also the infinite non-periodic sequence

$$
t = 0\,\mathrm{merge}(\mathrm{neg}(t), \mathrm{tail}(t)).
$$

Prove that the $n^{\mathrm{th}}$ digit of $t$ is the sum mod 2 of the digits of the number $n$ written in the binary scale (a suggestion of J. Lambek). Show also that $t \neq u\,a\,a\,a\,v$ where $a$ is any finite sequence $\neq \Lambda$, and where $u$ is finite.

<!-- page 92 -->

**[Exercise_5_16.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise_5_16.lean)**

@import "Exercise_5_16.lean"
**[NeighbourhoodSystems/TypedLambdaCalculus/Proposition_5_4.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition_5_4.lean)**

@import "Proposition_5_4.lean"
