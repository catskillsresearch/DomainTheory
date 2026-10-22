# Theorem 6.5

**THEOREM 6.5 (The $\mathfrak{F} \dot{\cap} \mathfrak{G}_\delta$ theorem).** *The sets that are intersections of closed sets with countable intersections of open sets are exactly the sets of the form:*

$$\{x \mid f(x) = a\},$$

*where $f : \mathbf{P}\omega \to \mathbf{P}\omega$ is continuous and $a$ is a fixed infinite set not equal to $\top$.*

Note that $(\mathfrak{F} \dot{\cap} \mathfrak{G})_\delta$ is the same class as $\mathfrak{F} \dot{\cap} \mathfrak{G}_\delta$, so we see by Theorem 6.4 that a good choice of $a$ is $\lambda n \in \omega . 0$.

There is no single subset of $\mathbf{P}\omega$ typical for $\mathfrak{B}$, which can be viewed as the finite unions of sets from the class $\mathfrak{F} \dot{\cap} \mathfrak{G}$.

**Lean 4**

- [DataTypesAsLattices/Classification/theorem_6_5.lean](theorem_6_5.lean)
- [DataTypesAsLattices/Classification/typicalFcapGdelta_isFcapGdelta.lean](typicalFcapGdelta_isFcapGdelta.lean)
- [DataTypesAsLattices/Classification/typicalFcapGdelta_universal.lean](typicalFcapGdelta_universal.lean)
- [DataTypesAsLattices/Classification.lean](../Classification.lean)
