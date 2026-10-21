# Theorem 6.1

**THEOREM 6.1 (The $\mathfrak{G}$ theorem).** *The open subsets of $\mathbf{P}\omega$ are exactly the sets of the form:*

$$\{x \mid f(x) \supseteq 0\},$$

*where $f : \mathbf{P}\omega \to \mathbf{P}\omega$ is continuous.*

We could have written $0 \in f(x)$ or the equation $f(x) \cap 0 = 0$ instead of $f(x) \supseteq 0$. Note that in case $f : \mathbf{P}\omega \to \{\bot, \top\}$, then $f(x) \supseteq 0$ is equivalent to $f(x) = \top$. Also any other integer could have been used in place of $0$.

We can say that $\{x \mid 0 \in x\}$ is the *typical* open set, and that every other open set can be obtained as an inverse image of the typical set by a continuous function. We shall extend this pattern to other classes, especially looking for equations. In the case of openness an inequality could also be used, giving as the typical set $\{x \mid x \neq \bot\}$. But since closed sets are just the complements of open sets, this remark gives us:

**Lean 4**

- [DataTypesAsLattices/Classification/theorem_6_1.lean](DomainTheory/DataTypesAsLattices/Classification/theorem_6_1.lean)
