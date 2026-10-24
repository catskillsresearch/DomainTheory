# Definition 6.4

## Human-English

**DEFINITION 6.4.** A ***T*-algebra** is a domain $E$ in the category together with a map

$$
k : T(E) \to E.
$$

If $m : T(F) \to F$ is another ***T*-algebra**, then a *homomorphism* is a map $h : E \to F$ in the category such that the diagram

$$
\begin{array}{ccc}
T(E) & \xrightarrow{k} & E \\
\downarrow^{T(h)} & & \downarrow^{h} \\
T(F) & \xrightarrow{m} & F
\end{array}
$$

commutes; that is, the equation

$$
h \circ k = m \circ T(h)
$$

holds. $\square$

<!-- page 103 -->

In our example from 6.1 a $T$-algebra is a *strict* map

$$k : D + (E \times E) \to E.$$

But such strict maps are in a one-one correspondence with pairs of (not necessarily strict) maps

$$n : D \to E \quad \text{and} \quad p : E \times E \to E.$$

And the structure $\langle E, n, p \rangle$ is what we called a tree algebra. Definition 6.4 just makes this abstract. The reader should also work out the details showing that 6.4's definition of homomorphism is just what we ought to expect.

Note that the $T$-algebras and homomorphisms form a category. (Why?) The following definition is so abstract that it could be given for any category.

## AI: Human-English to AI-Lean

**[Definition_6_4.lean](Definition_6_4.lean)**

@import "Definition_6_4.lean"
