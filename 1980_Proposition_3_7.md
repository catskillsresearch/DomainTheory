# Proposition 3.7

Said more informarily, a function of several arguments is approximable in all the variables *jointly* if it is approximable in each of the variables *separately*.

The type of argument used in 3.5 in the first half of the proof also provides a generalization of 2.6 to functions of several arguments. When we form a function like

$$
f(g(x, z, \ldots), h(y, x, \ldots), k(z, w, \ldots), \ldots)
$$

from given functions $f, g, h, k, \ldots$; we call the process *substitution*.

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
$$
f \circ \langle g \circ \langle p_0, p_1 \rangle, h \circ \langle p_1, p_2 \rangle, k \circ \langle p_3, p_0, p_2 \rangle \rangle ;
$$

and in fact this is the desired function. Writing it this way makes it clear that the function comes from an approximable mapping: we apply 3.3 (generalized, of course, to products with several terms) to construe the parts between brackets $\langle$ and $\rangle$ as approximable mappings, and then by this trick the composition $\circ$ is the ordinary composition of 2.6. $\square$
