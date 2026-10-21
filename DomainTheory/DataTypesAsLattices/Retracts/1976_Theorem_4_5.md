# Theorem 4.5

**THEOREM 4.5 (The sum theorem).** Suppose $a$, $b$, $a'$, $b'$ are retracts. Then we have:

(i) $a \oplus b$ is a retract, and it is always strict;

(ii) $u : a \oplus b$ iff $u = \bot$ or $u = \top$ or ($u = \langle 0, u_1 \rangle$ and $u_1 : a$) or ($u = \langle 1, u_1 \rangle$ and $u_1 : b$);

(iii) if $a \sqsubseteq a'$ and $b \sqsubseteq b'$, then $a \oplus b \sqsubseteq a' \oplus b'$;

(iv) if $f : a \circ\to b$ and $f' : a' \circ\to b'$, then $f \oplus f' : a \oplus a' \circ\to b \oplus b'$.

There are several combinators associated with $\oplus$:

$$(4.26) \quad \mathbf{inleft} = \lambda x.\, \langle 0, x \rangle;$$

$$(4.27) \quad \mathbf{inright} = \lambda x.\, \langle 1, x \rangle;$$

$$(4.28) \quad \mathbf{outleft} = \lambda u.\, u_0 \supset u_1,\, \bot;$$

$$(4.29) \quad \mathbf{outright} = \lambda u.\, u_0 \supset \bot,\, u_1;$$

$$(4.30) \quad \mathbf{which} = \lambda u.\, u_0;$$

$$(4.31) \quad \mathbf{out} = \lambda u.\, u_1.$$
(The last two are the same as **fst** and **snd**, but they will be used differently.) We find:

$$(4.32) \quad (a \oplus b) \circ \mathbf{inleft} \circ a : a \circ\to (a \oplus b);$$

$$(4.33) \quad (a \oplus b) \circ \mathbf{inright} \circ b : b \circ\to (a \oplus b);$$

$$(4.34) \quad a \circ \mathbf{outleft} \circ (a \oplus b) : (a \oplus b) \circ\to a;$$

$$(4.35) \quad b \circ \mathbf{outright} \circ (a \oplus b) : (a \oplus b) \circ\to b;$$

$$(4.36) \quad \mathbf{which} \circ (a \oplus b) : (a \oplus b) \circ\to \mathbf{bool};$$

$$(4.37) \quad a \circ \mathbf{out} \circ (a \oplus a) : (a \oplus a) \circ\to a;$$

where $a$ and $b$ are retracts. Most of these facts as they stand are trivial until one sets down the relations between all these maps; but there are too many to put them down here. Note, however, if $a$, $b$, and $c$ are retracts and $f : a \circ\to c$ and $g : b \circ\to c$, then if we let

$$h = c \circ \mathbf{out} \circ (f \oplus g),$$

we have:

$$h : (a \oplus b) \circ\to c,$$

and

$$h \circ \mathbf{inleft} = f \quad \text{and} \quad h \circ \mathbf{inright} = g.$$

But, though $h$ exists, it is not unique. So $a \oplus b$ is not the categorical sum (coproduct). The author does not know a neat categorical characterization of this operator.

There would be no difficulty in extending $\otimes$ and $\oplus$ to more factors by expanding the range of indices from $0, 1$ to $0, 1, \ldots, n-1$. The explicit formulae need not be given; but if we write $a_0 \otimes a_1 \otimes \cdots \otimes a_{n-1}$, we intend this expanded meaning rather than the iterated binary product.

To understand sums and other facts about retracts, consider the least fixed point of this equation:

$$(4.38) \quad \mathbf{tree} = \mathbf{nil} \oplus (\mathbf{tree} \otimes \mathbf{tree}).$$

To be certain that **tree** is a retract, we need a general theorem:

**Lean 4**

- [DataTypesAsLattices/Retracts/theorem_4_5.lean](DomainTheory/DataTypesAsLattices/Retracts/theorem_4_5.lean)
- [DataTypesAsLattices/Retracts/theorem_4_5_strict.lean](DomainTheory/DataTypesAsLattices/Retracts/theorem_4_5_strict.lean)
- [DataTypesAsLattices/Functionality/theorem_4_5_sum.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_4_5_sum.lean)
