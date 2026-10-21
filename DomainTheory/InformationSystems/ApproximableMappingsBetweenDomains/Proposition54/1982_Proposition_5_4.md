# Proposition 5.4

The proof is straightforward, and it completely justifies the use of the function-value notation. Consequently, the question arises as to whether the characterization of approximable mappings could not have been given in terms of elements in the first place. The answer is yes. Indeed, approximable mappings correspond exactly to functions on elements preserving unions of chains (this, in the case of countable information systems; directed unions must be used in general). This characterization has also been called “continuity,” because it is equivalent to saying that the mappings between elements are continuous mappings in the topological sense, when $|\mathbf{A}|$ and $|\mathbf{B}|$ are regarded as topological spaces, as explained in the last section. The reason for the word “approximable” is explained in Section 7.

Having justified the idea of an approximable mapping as a transformation on elements, the next step is to combine mappings. It is hardly surprising to learn that compositions of approximable mappings are approximable, which in mathematical terms means that the domains together with the approximable mappings form a *category*. The interesting part starts when we want to combine *domains*. But, to fix ideas, it is useful to spell out how compositions take place on the level of the data objects and consistent sets. For instance, it was noted that in any information system $\vdash$ is transitive on $\mathrm{Con}$, and in Definition 5.1 a transitivity condition comes in. There is a perfectly good reason for the parallelism, for, as we see next, the first idea (entailment) is a special case of the second (approximable mapping).

**PROPOSITION 5.4.** *Let $\mathbf{A}$ be an information system. Then the following formula defines an approximable mapping $I_{\mathbf{A}} : \mathbf{A} \to \mathbf{A}$:*

(i) $\quad u\ I_{\mathbf{A}}\ v \text{ iff } u \vdash_{\mathbf{A}} v,$

*for all $u, v \in \mathrm{Con}_{\mathbf{A}}$. And we have:*

(ii) $\quad I_{\mathbf{A}}(x) = x,$

*for all $x \in |\mathbf{A}|$.* $\blacksquare$

**Lean 4**

- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition54.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition54.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/Basic.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/Basic.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/idMap.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/idMap.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/idMap_toElement.lean](DomainTheory/InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/idMap_toElement.lean)
