# Proposition 6.7

**PROPOSITION 6.7.** If $i : T(D) \to D$ is an initial $T$-algebra, then so is $T(i) : T^2(D) \to T(D)$ and $i$ is the isomorphism from $T(D)$ to $D$.

**Proof:** Clearly since $T$ is a functor, the map $T(i)$ has the right mapping character to make $T(D)$ a $T$-algebra. Since $D$ is initial, we have a commuting diagram:

<!-- page 104 -->

$$
\begin{array}{ccc}
T(D) & \xrightarrow{i} & D \\
\downarrow^{T(j)} & & \downarrow^{j} \\
T^2(D) & \xrightarrow{T(i)} & T(D)
\end{array}
$$

But we also have the trivial diagram:

$$
\begin{array}{ccc}
T^2(D) & \xrightarrow{T(i)} & T(D) \\
\downarrow^{T(i)} & & \downarrow^{i} \\
T(D) & \xrightarrow{i} & D
\end{array}
$$

It follows that $i \circ j$ is a homomorphism, so

$$
i \circ j = I_D.
$$

But then because $T$ is a functor we find:

$$
T(i) \circ T(j) = I_{T(D)},
$$

and, since $j$ is a homomorphism, we have

$$
j \circ i = I_{T(D)}.
$$

This shows that $i$ is an isomorphism. $\square$

From 6.7 we see that if we are going to have initial algebras at all we have to satisfy the domain equation

$$
D \cong T(D).
$$

But generally that is not enough to assure that $D$ is initial. There is a condition that our functors satisfy, however, which guarantees the existence of homomorphisms.

**[Proposition_6_7.lean](Proposition_6_7.lean)**

@import "Proposition_6_7.lean"
