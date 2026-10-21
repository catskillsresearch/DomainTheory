# Proposition 5.6

In other words, composition of input/output relations is effected by putting the input into the first, getting some output, and then putting that in as input to the second. The correctness of this
recipe on elements (i.e. formula 5.5(ii)) follows from the basic formula 5.3(v). Because the class of all sets and arbitrary mappings forms a category—in the formal meaning of the word—the above three propositions show that the totality of information systems and approximable mappings also forms a category: a sub-category of the category of sets. We have given a special representation to the category by our use of data objects and consistent sets, and we have thereby put the elements into a secondary position—for a good reason. But the elements are there to use. The axioms for a category could also be verified directly using the basic definitions like 5.4(i) and 5.5(i); the details are bland. The more interesting topic is: what are the closure conditions on our domains; how do we construct new domains given old ones?

Before we go on to the first basic constructs of sums and products of domains, we remark on some other easy examples of approximable mappings: constant maps.

**PROPOSITION 5.6.** *Given information systems $\mathbf{A}$, $\mathbf{B}$, $\mathbf{C}$, and $\mathbf{D}$, and given a fixed element $b \in |\mathbf{B}|$, then there is a unique approximable mapping $\mathrm{const}\ b : \mathbf{A} \to \mathbf{B}$ such that:*

(i) $\quad (\mathrm{const}\ b)(x) = b,$

*for all $x \in |\mathbf{A}|$. Moreover, we have:*

(ii) $\quad f \circ (\mathrm{const}\ b) = \mathrm{const}\ f(b),$

*for all approximable mappings $f : \mathbf{B} \to \mathbf{C}$; and*

(iii) $\quad (\mathrm{const}\ b) \circ g = \mathrm{const}\ b,$

*for all approximable mappings $g : \mathbf{D} \to \mathbf{A}$.* $\blacksquare$

**Lean 4**

- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition56.lean](../Proposition56.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/Basic.lean](Basic.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/comp_constMap.lean](comp_constMap.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/constMap.lean](constMap.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/constMap_comp.lean](constMap_comp.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/constMap_toElement.lean](constMap_toElement.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/constMap_unique.lean](constMap_unique.lean)
