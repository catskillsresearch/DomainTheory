# Exercise 4.24

**EXERCISE 4.24.** (For set theorists). Let $f : A \to B$ and $g : B \to A$ be one-one functions (into, not necessarily onto!) Prove the Schroeder - Bernstein theorem to the effect that there exists a one-one correspondence $h : A \leftrightarrow B$. (Hint: (Suggested by A. Tarski). By the fixed-point theorem find $X \subseteq A$ where

$$
X = (A - g(B)) \cup g(f(X)),
$$

where $f(X) =$ the image of the set $X$ under the function $f$. Define $h \subseteq A \times B$ as a union of two restrictions:

$$
h = f \upharpoonright X \cup g^{-1} \upharpoonright (A - X).
$$

A picture helps.)

**[Exercise_4_24.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise_4_24.lean)**

@import "Exercise_4_24.lean"
