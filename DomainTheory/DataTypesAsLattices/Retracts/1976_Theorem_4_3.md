# Theorem 4.3

**THEOREM 4.3 (The function space theorem).** Suppose $a, b, a', b', c$ are retracts. Then we have:

(i) $a \circ\to b$ is a retract, and it is strict if $b$ is;

(ii) $u : a \circ\to b$ iff $u = \lambda x : a.\, u(x)$ and $\forall x : a.\, u(x) : b$;

(iii) if $a \sqsubseteq a'$ and $b \sqsubseteq b'$, then $a \circ\to b \sqsubseteq a' \circ\to b'$;

(iv) if $f : a \circ\to b$ and $f' : a' \circ\to b'$, then $f \circ\to f' : (b \circ\to a') \circ\to (a \circ\to b')$;

(v) if $f : a \circ\to b$ and $f' : b \circ\to c$, then $f' \circ f : a \circ\to c$.

Parts (i), (iii), (iv), and (v) can be proved using (4.8) and (4.11) in an algebraic (formal) fashion. It is (ii) that tells us what it all means: the range of $a \circ\to b$ consists exactly of those functions which are restricted to (the range of) $a$ and which have values in $b$. So we can read $u : a \circ\to b$ in the normal way: $u$ is a (continuous) mapping from $a$ into $b$. In technical jargon, we can say that the (strict) retracts and continuous functions form a *category*. In fact, it is equivalent to the category of separable continuous lattices and continuous maps. In this context, (iv) shows that $\circ\to$ operates not only on spaces (retracts) but also on maps: it is a functor contravariant in the first argument and covariant in the second. Further categorical properties will emerge.

**Lean 4**

- [DataTypesAsLattices/Retracts/theorem_4_3.lean](theorem_4_3.lean)
- [DataTypesAsLattices/Retracts/theorem_4_3_i.lean](theorem_4_3_i.lean)
- [DataTypesAsLattices/Retracts/theorem_4_3_ii.lean](theorem_4_3_ii.lean)
