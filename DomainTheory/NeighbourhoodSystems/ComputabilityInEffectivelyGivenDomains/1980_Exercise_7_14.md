# Exercise 7.14

## Human-English

**EXERCISE 7.14.** (For recursive-function theorists.) Prove the statements after definition 7.2 about the existence of primitive recursive functions for showing things recursively enumerable. (Recall that a non-empty set is r.e. iff it is the range of a primitive recursive function.) Show also that every computable element $y \in |E|$ can be written

$$y = \bigcup \{ \uparrow Y_{t(i)} \mid i \in \mathbf{N} \},$$

where $t : \mathbf{N} \to \mathbf{N}$ is primitive recursive and where we may assume

<!-- page 131 -->

$Y_{t(i+1)} \subseteq Y_{t(i)}$

for all $i \in \mathbf{N}$.

## AI: Human-English to AI-Lean

**[Exercise_7_14.lean](Exercise_7_14.lean)**

@import "Exercise_7_14.lean"
