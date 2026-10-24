# Exercise 2.14

## Human-English

**EXERCISE 2.14.** Let $f : |D_0| \to |D_1|$ be an isomorphism between domains. Let $\varphi : D_0 \to D_1$ be the one-one correspondence between neighbourhoods provided by Theorem 2.7 where

$$
f(\uparrow X) = \uparrow \varphi(X)
$$

for all $X \in D_0$. Show that the approximable mapping determined by $f$ is just the relationship $\varphi(X) \subseteq Y$. In addition prove that if $X, X' \in D_0$ are consistent, then

$$
\varphi(X \cap X') = \varphi(X) \cap \varphi(X').
$$

<!-- page 34 -->

Remark that the isomorphisms between domains correspond exactly to the isomorphisms between neighbourhood systems (in the sense of one-one inclusion preserving correspondences).

## AI: Human-English to AI-Lean

**[Exercise_2_14.lean](Exercise_2_14.lean)**

@import "Exercise_2_14.lean"
