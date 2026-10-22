# Theorem 7.2

**THEOREM 7.2 (The isomorphism theorem).** *If $a$ and $b$ are retracts, we have the following isomorphisms and identities relating the spaces:*

(i) $E_a \cong \{\langle x, y \rangle \mid a(x) = a(y)\}$;

(ii) $E_{a \circ\to b} \cong E_a \to E_b$;

(iii) $E_{a \otimes b} = E_a \times E_b$;

(iv) $E_{a \oplus b} = E_a + E_b \cup \{\langle \bot, \bot \rangle, \langle \top, \top \rangle\}$.

Part (iv) is not categorical in nature as it stands, but (ii) and (iii) indicate that $E$ is a functor from the category of retracts into the category of equivalence relations that shows that the former is a full sub-Cartesian-closed category of the latter. We cannot pursue the categorical questions here, but note that there are many subcategories that might be of interest; for example, the equivalence relations with the intersection property are closed under $\to$, $\times$, and $+$.

Returning to the question of total functions we introduce this notation:

$$(7.9) \quad N = \{\langle n, n \rangle \mid n \in \omega\}.$$

This is the type of the integers *without* $\bot$ and $\top$, i.e., the total integers. We note that:

$$(7.10) \quad N = \{u \mid u = \langle u_0, u_0 \rangle,\, u_0 = \mathbf{int}(u_0),\, \mathbf{mid}(u_0) = 0\}.$$

Thus $N$ is a $\mathfrak{B}_\delta$-set. What is $N \to N$? We see:

$$(7.11) \quad f : N \to N \text{ iff } f : \mathbf{fun} \text{ and } f(n) \in \omega \text{ whenever } n \in \omega.$$

This $N \to N$ is indeed the type of all total functions from $\omega$ into $\omega$. It can be shown that $N \to N$ is also a $\mathfrak{B}_\delta$-set: good. But what is $(N \to N) \to N$? This is no longer a $\mathfrak{B}_\delta$-set, the best we can say is $\Pi_1^1$. By Theorem 7.1 it corresponds to the type of all
(extensional) *continuous* total functions from $N \to N$ into $N$. (The condition on $A$ and $B$ on the right side of (7.6) makes the concept of function embodied in $A \to B$ extensional, since the functions are meant to preserve the equivalence relations.)

A more precise discussion identifies $N \to N$ as a topological space, usually called the *Baire space*. If we introduce the finite discrete spaces by:

$$(7.12) \quad N_k = \{\langle n, n \rangle \mid n < k\},$$

then $N \to N_2$ can also be identified with a topological space, usually called the *Cantor space*. In this identification we find at the next type, say either $(N \to N) \to N$ or $(N \to N_2) \to N_2$, that elements correspond to the usual notion of continuous function defined in topological terms. However, these higher type spaces are not at all conveniently taken as *topological* spaces. Certain of them can be identified as *limit spaces* according to the work of Hyland, and for these $\to$, $\times$, and $+$ have the natural interpretation. We cannot enter into these details here, but we can remark that the higher type spaces become ever more complicated. Thus $((N \to N) \to N) \to N$ is a $\Pi_2^1$-set and each $\to$ will add another quantifier to the definition. This is reasonable, because to say that a function is total is to say that *all* its values are well-behaved. But if its domain is a complex space, this statement of totality is even more complex. Despite this complexity, however, it is possible to sort out what kind of mapping properties many functions have. We shall mention a few of the combinators.

**Lean 4**

- [DataTypesAsLattices/Functionality/theorem_7_2_i.lean](theorem_7_2_i.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_i_iso.lean](theorem_7_2_i_iso.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_ii_of_typed.lean](theorem_7_2_ii_of_typed.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_ii.lean](theorem_7_2_ii.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_iii.lean](theorem_7_2_iii.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_iii_exact.lean](theorem_7_2_iii_exact.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_iv.lean](theorem_7_2_iv.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2.lean](theorem_7_2.lean)
