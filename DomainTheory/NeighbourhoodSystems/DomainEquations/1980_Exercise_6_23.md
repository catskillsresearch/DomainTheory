# Exercise 6.23
**[NeighbourhoodSystems/DomainEquations/Exercise_6_23.lean](Exercise_6_23.lean)**

@import "exprDomain.lean" {code_block=false}

@import "Exercise_6_23.lean"

**EXERCISE 6.23.** Construe the initial solution to

$$
\mathit{Exp} \cong N \oplus ((\mathit{Exp} \times \mathit{Exp}) + (\mathit{Exp} \times \mathit{Exp}))
$$

as a “syntactical domain” of expressions generated from infinitely many “variables” by means of two binary “operation symbols”. Given an algebra $D$ with two operations

$$
u : D \times D \to D \quad \text{and} \quad v : D \times D \to D,
$$

show how any strict map $s : N \to D$ determines a unique map

$$
\mathit{val}(s) : \mathit{Exp} \to D
$$

that can be regarded as the “evaluation of an expression”.

<p style="color:#15803d;margin-top:1em;">✓ <strong>Revised</strong> (2026-11-07) — <a href="../1980_REVISION.md">1980 revision progress</a></p>
