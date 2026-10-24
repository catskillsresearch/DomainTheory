# Proposition 3.7

## Human-English

**PROPOSITION 3.7.** The functions of several arguments between domains coming from approximable mappings are closed under substitution.

*Proof:* An example will establish the method. Suppose there are four variables involved taking values in domains provided by systems $D_0, D_1, D_2, D_3$. We might have a substitution like:

$$
f(g(x_0, x_1), h(x_1, x_2), k(x_3, x_0, x_2)).
$$

Here it might be that the values of the functions inside come from quite other systems; for instance,

$$
k : D_3 \times D_0 \times D_2 \to D_4
$$

might be possible. By using projections

$$
p_i : D_0 \times D_1 \times D_2 \times D_3 \to D_i,
$$

where $i < 4$, we can assure that we have several functions all on the same product; thus,

$$
k \cdot \langle p_3, p_0, p_2 \rangle : D_0 \times D_1 \times D_2 \times D_3 \to D_4.
$$

Now no matter on what domains $f$ is defined, the following composition makes sense:

<!-- page 42 -->

$$
f \circ \langle g \circ \langle p_0, p_1 \rangle, h \circ \langle p_1, p_2 \rangle, k \circ \langle p_3, p_0, p_2 \rangle \rangle ;
$$

and in fact this is the desired function. Writing it this way makes it clear that the function comes from an approximable mapping: we apply 3.3 (generalized, of course, to products with several terms) to construe the parts between brackets $\langle$ and $\rangle$ as approximable mappings, and then by this trick the composition $\circ$ is the ordinary composition of 2.6. $\square$

It has to be admitted that there is a slight point overlooked in forming products like $D \times D$ with two identical domains. This is discussed in Exercise 3.14, invoking explicit isomorphisms.

The construct that makes the whole theory of domains work so smoothly is the function-space construct: it is possible to regard functions as *objects* which form a domain. Look back at Definition 2.1 and compare it with the original definition of element in 1.6. There are obvious formal similarities, except that filters are sets of neighbourhoods and mappings are sets of pairs of neighbourhoods (relations). But as we saw in 1.10 it is possible to turn the filters into tokens via a simple definition of neighbourhood. We apply the same kind of definition to the mappings.

## AI: Human-English to AI-Lean

**[Proposition_3_7.lean](Proposition_3_7.lean)**

@import "Proposition_3_7.lean"
