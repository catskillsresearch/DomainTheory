# Proposition 5.5

In other words, the given entailment relation itself defines the identity function on the domain in question; and of course, the identity function is an approximable mapping.

**PROPOSITION 5.5.** *Let $f : \mathbf{A} \to \mathbf{B}$ and $g : \mathbf{B} \to \mathbf{C}$ be two approximable mappings. Then the following formula defines an approximable mapping $g \circ f : \mathbf{A} \to \mathbf{C}$:*

(i) $\quad u\ (g \circ f)\ w \text{ iff } u\ f\ v \text{ and } v\ g\ w \text{ for some } v \in \mathrm{Con}_{\mathbf{B}},$

*for all $u \in \mathrm{Con}_{\mathbf{A}}$ and $w \in \mathrm{Con}_{\mathbf{C}}$. And we have:*

(ii) $\quad (g \circ f)(x) = g(f(x)),$

*for all $x \in |\mathbf{A}|$.* $\blacksquare$

**Lean 4**

- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition55/comp.lean](comp.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition55/Basic.lean](Basic.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition55/comp_toElement.lean](comp_toElement.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition55.lean](../Proposition55.lean)
