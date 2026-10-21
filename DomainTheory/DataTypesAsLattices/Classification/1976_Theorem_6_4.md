# Theorem 6.4

**THEOREM 6.4 (The $\mathfrak{F} \dot{\cap} \mathfrak{G}$ theorem).** *The sets that are intersections of closed sets with open sets are exactly the sets of the form:*

$$\{x \mid f(x) = 0\},$$

*where $f : \mathbf{P}\omega \to \mathbf{P}\omega$ is continuous.*

Again it may not be obvious that every $\mathfrak{F} \dot{\cap} \mathfrak{G}$ set has this form. We can write:

$$C = \{x \mid f(x) = \bot\},$$

and

$$U = \{x \mid g(x) = 0\},$$

where $C \in \mathfrak{F}$ and $U \in \mathfrak{G}$ and the continuous $f$ and $g$ are suitably chosen. Define

$$h(x) = \{2n + 1 \mid n \in f(x)\} \cup \{2n \mid n \in g(x)\},$$

and remark that $h$ is continuous. We have:

$$C \cap U = \{x \mid h(x) = 0\},$$

as desired.

It is easy to see that $\{e\} \in \mathfrak{F} \dot{\cap} \mathfrak{G}$ if $e$ is finite, but in general $\{a\} \notin \mathfrak{F} \dot{\cap} \mathfrak{G}_\delta$.

In case $a$ is infinite but not equal to $\top$ (say, $a = \{n \mid n > 0\} = \top + 1$), then $\{a\}$ is typical in its class.

**Lean 4**

- [DataTypesAsLattices/Classification/theorem_6_4.lean](theorem_6_4.lean)
