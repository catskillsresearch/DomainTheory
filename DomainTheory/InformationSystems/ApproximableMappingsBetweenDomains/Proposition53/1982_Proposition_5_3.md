# Proposition 5.3

**PROPOSITION 5.3.** *Let $f, g : \mathbf{A} \to \mathbf{B}$ be two approximable mappings between two information systems. Then*

*(i) $f$ always maps elements to elements under Definition 5.2;*

*(ii) $f = g$ iff $f(x) = g(x)$ for all $x \in |\mathbf{A}|$; and*

*(iii) $f \subseteq g$ iff $f(x) \subseteq g(x)$ for all $x \in |\mathbf{A}|$.*

Moreover, the approximable mappings are monotone in the sense that

(iv) $x \subseteq y$ in $|\mathbf{A}|$ always implies $f(x) \subseteq f(y)$ in $|\mathbf{B}|$.

*All these results follow from the observation that*
(v) $\quad u\ f\ v \text{ iff } \bar{v} \subseteq f(\bar{u}),$

for all $u \in \mathrm{Con}_{\mathbf{A}}$ and all $v \in \mathrm{Con}_{\mathbf{B}}$. $\blacksquare$

**Lean 4**

- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition53.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition53.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/Basic.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/Basic.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/Le.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/Le.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/ext_iff_toElement.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/ext_iff_toElement.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/le_iff_toElement_le.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/le_iff_toElement_le.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/rel_iff_closure_le.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/rel_iff_closure_le.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/rel_iff_forall_singleton.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/rel_iff_forall_singleton.lean)
