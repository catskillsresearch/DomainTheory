# Proposition 3.4

**PROPOSITION 3.4.** The mappings $p_0$, $p_1$ and $\langle f, g \rangle$ are approximable mappings, provided $f$ and $g$ are, and we have:

(i) $p_0 \circ \langle f, g \rangle = f$ and $p_1 \circ \langle f, g \rangle = g$.

Moreover, for $z \in |\mathcal{D}_0 \times \mathcal{D}_1|$, we have:

(ii) $p_0(z) = z_0$ and $p_1(z) = z_1$,

in the notation of the proof of 3.2. Further if $h : \mathcal{D}_2 \to \mathcal{D}_0 \times \mathcal{D}_1$ is any approximable mapping, then

(iii) $h = \langle p_0 \circ h, p_1 \circ h \rangle$.

Moreover, for all $w \in |\mathcal{D}_2|$, we have:

(iv) $\langle f, g \rangle(w) = \langle f(w), g(w) \rangle$,

where again on the right-hand side the notation of the proof of 3.2 is used. $\square$

The proof of this result is left as an exercise. Note the consequence that there is a one-one correspondence between pairs of approximable mappings $f : \mathcal{D}_2 \to \mathcal{D}_0$ and $g : \mathcal{D}_2 \to \mathcal{D}_1$ and mappings $h : \mathcal{D}_2 \to \mathcal{D}_0 \times \mathcal{D}_1$. It is clear that we generalize all this to products

$$
\mathcal{D}_0 \times \mathcal{D}_1 \times \cdots \times \mathcal{D}_{n-1}
$$

of several systems.

The product construct also neatly explains functions of several variables. In Exercise 2.19 we used the informal notation

$$
f : \mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}_2
$$

and suggested regarding $f$ as a ternary relation

$$
X, Y\ f\ Z.
$$

But now with $\mathcal{D}_0 \times \mathcal{D}_1$ given an independent meaning, all we have to do is to regard $f$ as a binary relation with

$$
(X, Y)\ f\ Z
$$

equivalent to the old relationship. We can also employ an element-wise notation as in $f(\langle x, y \rangle)$, which can more easily be written $f(x, y)$. Similar remarks apply to functions of more than two arguments.

<!-- page 40 -->

We have discussed several times what it means for a function $f(x)$ to come from an approximable mapping. It is interesting to ask the analogous question for functions of several arguments.

**[Proposition_3_4.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Proposition_3_4.lean)**

@import "Proposition_3_4.lean"
