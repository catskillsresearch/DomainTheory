# Theorem 3.4

**THEOREM 3.4 (The incompleteness theorem).** The set of integers $n$ such that $\mathbf{val}(n) = \bot$ is not r.e.; hence, there can be no effectively given formal system for enumerating all true equations between LAMBDA-terms.

(A critic may sense here an application of Church's thesis in stating the metatheoretic consequence of the nonresult.) A few details of the proof can be given to see how the notation works. First let $v$ be a (total) primitive recursive function such that:

$$\mathbf{val}(v(n)) = n \cap \mathbf{val}(n),$$

and note that:

$$n \cap \mathbf{val}(n) = \bot \quad \text{iff} \quad n \notin \mathbf{val}(n).$$

Call the set in question in Theorem 3.4 the set $b$. If it were r.e., then so would be:

$$\{n \in \omega \mid v(n) \in b\} = (\lambda n \in \omega.\, v(n) \cap b \supset n, n)(\top).$$

That would mean having an integer $k$ such that:

$$\mathbf{val}(k) = \{n \in \omega \mid v(n) \in b\}.$$

But then:

$$
\begin{aligned}
k \in \mathbf{val}(k) &\iff v(k) \in b \\
&\iff \mathbf{val}(v(k)) = \bot \\
&\iff k \notin \mathbf{val}(k),
\end{aligned}
$$

which gives us a contradiction. This is the usual diagonal argument.

The relationship $\mathbf{val}(n) = \mathbf{val}(m)$ means that the expressions with Gödel numbers $n$ and $m$ have the same value in the model. (This is not only not r.e. but is a complete $\Pi_2^0$-predicate.) A *total* mapping can be regarded as a *syntactical* transformation on expressions defined via Gödel numbers. Such a mapping $p$ is called *extensional* if it has the property:

$$\mathbf{val}(p(n)) = \mathbf{val}(p(m)) \quad \text{whenever} \quad \mathbf{val}(n) = \mathbf{val}(m).$$

The Myhill–Shepherdson theorem shows that extensional, syntactical mappings really depend on the *values* of the expressions. Precisely we have:

**Lean 4**

- [DataTypesAsLattices/Enumeration/theorem_3_4.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_4.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_4_diagonal.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_4_diagonal.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_4_re_diagonal.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_4_re_diagonal.lean)
