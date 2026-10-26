# Factoid 1.7

## Factoid 1.7a1 — principals are one-one

It is obvious that the correspondence between $X$ and $\uparrow X$ is one-one and inclusion *reversing*, in the sense that

## Factoid 1.7a2 — inclusion-reversing principals

$$
X \subseteq Y \quad \text{iff} \quad \uparrow Y \subseteq \uparrow X
$$

for all $X, Y \in \mathcal{D}$. But, except in very special cases, there is much more to $|\mathcal{D}|$ than just the finite elements. Much of our investigation will be concerned with finding out how much more. The finite elements are, in a certain sense, "dense" in $|\mathcal{D}|$, however, because it is also obvious from the definitions that for each $x \in |\mathcal{D}|$

## Factoid 1.7b — union of principal filters

$$
x = \bigcup \{ \uparrow X \mid X \in x \}.
$$

That is, every element is a certain type of "limit" of finite elements. (This statement is made more precise in Exercise 1.21)

We note that we have now had several occasions to use inclusion relationships between elements; this is an important relationship, and we give it a special name.

<!-- page 14 -->

**[Factoid_1_7.lean](Factoid_1_7.lean)**

@import "Factoid_1_7.lean"
