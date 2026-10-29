# Exercise 7.24

**EXERCISE 7.24.** (Suggested by the LUCID language of Ashcroft and Wadge: SIAM Jour. Comp. vol. 5 (1976).)

Define a set $\Gamma$ by

$$\Gamma = \bigcup_{i=0}^{\infty} (\{i\} \times \Gamma) \cup \{\star\}.$$

Define a system

$$L = \{\Gamma\} \cup \{ \{i\} \times X \mid i \in \mathbf{N} \text{ and } X \in L \}.$$

Show that $L$ is effectively given. Show that the elements of $|L|$ can be identified with the finite and infinite sequences of natural numbers. What is the connection between $B$ and $L$?

Show that the combinators of LUCID can be construed as computable mappings of type

$$(L \to T) \to (L \to T)$$

or of type

$$(L \to T) \times (L \to T) \to (L \to T).$$

Conclude that programs in LUCID define computable maps.

<!-- page 135 -->

**[Exercise_7_24.lean](Exercise_7_24.lean)**

@import "Exercise_7_24.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem_7_6.lean](Theorem_7_6.lean)**

@import "Theorem_7_6.lean"
