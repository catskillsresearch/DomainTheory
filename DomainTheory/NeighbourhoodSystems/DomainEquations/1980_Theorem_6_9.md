# Theorem 6.9

## Human-English

**THEOREM 6.9.** If the functor $T$ is continuous on maps and if $D \cong T(D)$, so in particular $D$ is a $T$-algebra, then for any $T$-algebra $k : T(E) \to E$ there is a homomorphism $h : D \to E$.

*Proof:* Let $i : T(D) \to D$ make $D$ a $T$-algebra, where $j : D \to T(D)$ is the inverse so that $i$ is an isomorphism of domains. Suppose that $k : T(E) \to E$ is any $T$-algebra. A homomorphism $h : D \to E$ would satisfy

$$
h \circ i = k \circ T(h).
$$

Rewrite this equation as

$$
h = k \circ T(h) \circ j.
$$

In the domain of strict maps $(D \to E)$ this is a fixed-point equation for an approximable map

$$
\lambda h.\, k \circ T(h) \circ j
$$

by our assumption on $T$. Thus, the desired homomorphism exists. $\square$

The final question we have to answer is why in our category the minimal $D$ exist. The reason is that the functors $T$ that we have in mind possess further continuity properties on domains. This is conveniently expressed in terms of a notion of "subdomain".

## AI: Human-English to AI-Lean

**[Theorem_6_9.lean](Theorem_6_9.lean)**

@import "Theorem_6_9.lean"
