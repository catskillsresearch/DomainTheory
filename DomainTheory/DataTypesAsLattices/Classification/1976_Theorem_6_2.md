# Theorem 6.2

**THEOREM 6.2 (The $\mathfrak{F}$ theorem).** *The closed subsets of $\mathbf{P}\omega$ are exactly the sets of the form:*

$$\{x \mid f(x) = \bot\},$$

*where $f : \mathbf{P}\omega \to \mathbf{P}\omega$ is continuous.*

Aside from $\{x \mid x = \bot\}$, we could have used $\{x \mid x \subseteq a\}$ as the typical closed set where $a \in \mathbf{P}\omega$ is any element whatsoever aside from $\top$. This $\top$ has, by the way, a special character. We note:

$$\{\top\} = \bigcap \{\{x \mid n \in x\} \mid n \in \omega\}.$$

Thus $\{\top\}$ is a countable intersection of open sets, otherwise called a $\mathfrak{G}_\delta$-set. There are of course many other $\mathfrak{G}_\delta$-sets, but $\{\top\}$ is the typical one:

**Lean 4**

- [DataTypesAsLattices/Classification/theorem_6_2.lean](theorem_6_2.lean)
- [DataTypesAsLattices/Classification/typicalF_mem_ScottF.lean](typicalF_mem_ScottF.lean)
- [DataTypesAsLattices/Classification/typicalF_universal.lean](typicalF_universal.lean)
