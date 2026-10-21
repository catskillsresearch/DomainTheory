# Theorem 3.5

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
We have discussed several times what it means for a function $f(x)$ to come from an approximable mapping. It is interesting to ask the analogous question for functions of several arguments.

**THEOREM 3.5.** An elementwise function
$$f : |D_0 \times D_1| \to |D_2|$$
of two arguments comes from an approximable mapping iff for each fixed $a \in |D_0|$ and each fixed $b \in |D_1|$ the transformations
$$x \mapsto f(x, b) \quad \text{and} \quad y \mapsto f(a, y)$$
come from approximable mappings of one argument.

*Proof:* As this is the first time we have had to deal with constants in functions, a lemma is useful.
