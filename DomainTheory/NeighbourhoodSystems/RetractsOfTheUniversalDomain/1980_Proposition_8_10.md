# Proposition 8.10

**PROPOSITION 8.10.** If $a, b : \mathcal{U} \to \mathcal{U}$ are projections, then so are $a + b$, $a \times b$, and $a \to b$. If $a$ and $b$ are finitary, then so are the others; for the fixed-point set of each of them is isomorphic to the corresponding construct applied to the domains determined by $a$ and $b$.

<!-- page 144 -->

*Proof:* Suppose that $a, b \sqsubseteq I_{\mathcal{U}}$ (= $I$ for short). Then

$$a + b \sqsubseteq I + I = i_+ \circ j_+ \sqsubseteq I.$$

The other cases are similar.

Suppose $a = a \circ a$ and $b = b \circ b$, then, for example,

$$
\begin{aligned}
(a \times b) \circ (a \times b) &= i_\times \circ \langle a \circ \mathrm{proj}_0,\ b \circ \mathrm{proj}_1 \rangle \circ \langle a \circ \mathrm{proj}_0,\ b \circ \mathrm{proj}_1 \rangle \circ j_\times \\
&= i_\times \circ \langle a \circ a \circ \mathrm{proj}_0,\ b \circ b \circ \mathrm{proj}_1 \rangle \circ j_\times \\
&= a \times b.
\end{aligned}
$$

The other cases are similar.

Now in case the fixed-point sets of $a$ and $b$ are domains, they are respectively isomorphic to

$$D_a = \{ X \in \mathcal{U} \mid X \ a \ X \} \quad \text{and}$$
$$D_b = \{ Y \in \mathcal{U} \mid Y \ b \ Y \}.$$

We have to show, for example, that

$$D_a \to D_b \cong D_{a \to b}.$$

Now to simplify matters, remark that the fixed-point set of $a \to b$ on $\mathcal{U}$ is isomorphic to the fixed-point set of $\lambda f.\ b \circ f \circ a$ on $(\mathcal{U} \to \mathcal{U})$. (Hint: use $i_\to$ and $j_\to$ to set up the isomorphism.) So we have to think what it is for an $f : \mathcal{U} \to \mathcal{U}$ to satisfy

$$f = b \circ f \circ a.$$

Notice that we might as well say that $a : \mathcal{U} \to D_a$ and that this map is the other half of an obvious projection pair where

$$i_a : D_a \to \mathcal{U},$$

and $i_a \circ a = a$ and $a \circ i_a = i_a$. So if $g : D_a \to D_b$, let

$$f = i_b \circ g \circ a;$$

then $b \circ f \circ a = f$. Conversely, if $f$ is like this, then let

$$g = b \circ f \circ i_a.$$

Thus, $i_b \circ g \circ a = b \circ f \circ a = f$; so there is an order-preserving isomorphism between the $g : D_a \to D_b$ and the $f = b \circ f \circ a$.

<!-- page 145 -->

The isomorphism proofs for $+$ and $\times$ are similar. $\square$

Well, this was a lot of work, but the pay-off is rather handsome. What we have done is transpose all the

$$D_a \triangleleft U$$

over to finitary projections $a : U \to U$. This transposition is an isomorphism, because

$$D_a \triangleleft D_b \text{ iff } a \sqsubseteq b.$$

Moreover, by the method of 8.9 and 8.10, all our favourite constructs have been made into *combinators*, that is, approximable — even computable — maps on the domain of finitary projections. *ALL APPROXIMABLE (COMPUTABLE) MAPS HAVE (COMPUTABLE) FIXED POINTS.* And there you are! The standard fixed-point method is available to obtain computable (i.e. effectively given) solutions to *all* domain equations (even sets of equations) where the constructs can be reworked in *this* way to be defined on projections. Examples are suggested in the exercises.

Another pay-off concerns the $\lambda$-calculus itself. Inasmuch as

$$U + U, \quad U \times U, \quad U \to U \triangleleft U,$$

we might just as well forget the outside world and regard all these useful domains as being part of $U$. For example, on the left we have the new notation and on the right the old notation:

$$
\begin{aligned}
\mathrm{which}(z) &= \mathrm{which}(j_+(z)) ; \\
\mathrm{in}_i(x) &= i_+(\mathrm{in}_i(x)), \quad i = 0, 1 ; \\
\mathrm{out}_i(x) &= \mathrm{out}_i(j_+(x)), \quad i = 0, 1 ; \\
\langle x, y \rangle &= i_\times(\langle x, y \rangle) ; \\
\mathrm{proj}_i(z) &= \mathrm{proj}_i(j_\times(z)), \quad i = 0, 1 ; \\
u(x) &= j_\to(u)(x) ; \\
\lambda x.\,\tau &\cong i_\to(\lambda x.\,\tau) .
\end{aligned}
$$

And, there is no reason to stop here. The system

$$T \cong \{\{0, 1/2\}, \{1/2, 1\}, \{0, 1\}\} \triangleleft U,$$

so we might as well think of

<!-- page 146 -->

$$\text{true, false} \in |U|$$

and think of $\mathrm{cond} : U \times U \times U \to U$. No! that is wrong: under the new regime *EVERYTHING IS AN ELEMENT OF U*. With the new meaning of $\lambda$, all functions, all pairs, all combinators, all constructs become elements of $U$.

It takes a little time to get used to "universal conscription" with all elements doing (at least) double duty in the same domain, but there are many advantages, both notational and conceptual.

**[Proposition_8_10.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition_8_10.lean)**

@import "Proposition_8_10.lean"
