# Factoid 1.1

## Factoid 1.1a — empty intersection is delta

$$
\bigcap_{i < n} X_i = \Delta, \text{ if } n = 0;
$$

## Factoid 1.1b — recursive finite intersection

$$
= \left(\bigcap_{i < n-1} X_i\right) \cap X_{n-1}, \text{ if } n > 0.
$$

Of course, from (ii), we can extend the intersection property to any finite sequence. Consequently, we can say $X_0, \dots, X_{n-1}$ is consistent in $\mathcal{D}$ iff

$$
\bigcap_{i < n} X_i \in \mathcal{D}.
$$

Some examples will help us understand the notions better.

## AI: Human-English to AI-Lean

**[Factoid_1_1.lean](Factoid_1_1.lean)**

@import "Factoid_1_1.lean"
