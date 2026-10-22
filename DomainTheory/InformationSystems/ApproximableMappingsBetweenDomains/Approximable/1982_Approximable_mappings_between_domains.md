# Approximable mappings between domains

Once a general notion of set or domain has been defined mathematically, the next major issue is: How are the different domains to be related one to another? The answer to this important question can many times be given by defining an appropriate concept of mapping between domains. The answer need not be unique; the same collection of domains may support more than one idea of function depending on the special aspects of the domains that need to be brought out. In the case of the kinds of domains being studied here, there are two principal answers, one of which is to be explained in this section.

In order to understand an appropriate notion of a mapping or a function between domains constructed from information systems, we have to refer back to the way in which elements are introduced. As we have seen in Section 3, an element is a consistent, closed set of data objects. To generate an element, one has to generate more and more of the finite consistent subsets of the element. Note that the separate data objects have to be grouped into these finite consistent sets, because the entailment relation may require a finite set of arbitrary size on the left in making the necessary entailments for closure. It is this kind of passage from a finite set to its closure that is to be generalized in defining mappings.

Consider two domains. To map from one to another, some information about a possible element of the first is presented as input to the function $f$. Then as output the function $f$ starts generating an element. If the input were $u$, a consistent set of the first domain, then part of the output in the second domain might be a consistent set $v$. We could say that there is an input/output relationship set up by $f$, and indicate by $u\ f\ v$ that this relation holds going from $u$ in the first domain to $v$ in the second. Of course to get the full effect of $f$, it is necessary to take all the $v$'s related to a given $u$, because even a small finite amount of input may cause an infinite amount of output. But every element of a domain is just the sum total of its finite subsets (finite approximations), so it is sufficient to make the mapping relationship go between finite sets. Here is the formal definition with the exact conditions that the relation $f$ must satisfy.

- [Definition 5.1](1982_Definition_5_1.md)
- [Definition 5.2](1982_Definition_5_2.md)
- [Proposition 5.3](../Proposition53/1982_Proposition_5_3.md)
- [Proposition 5.4](../Proposition54/1982_Proposition_5_4.md)
- [Proposition 5.5](../Proposition55/1982_Proposition_5_5.md)
- [Proposition 5.6](../Proposition56/1982_Proposition_5_6.md)

The proof is immediate, since we need only interpret the input/output relation $u\ (\mathrm{const}\ b)\ v$ as meaning $v \subseteq b$. We note that our notation is somewhat ambiguous since, for example, in 5.6(iii) we are using $\mathrm{const}\ b$ in two senses: once as a mapping from $\mathbf{A}$, and once as a mapping from $\mathbf{D}$. In fact, we should hang two subscripts on the thing to fix both the source and the target of the mapping. This is too painful, however, and we generally rely on context to make the meaning clear. (Formal rules of type checking can be given, so on a computer-based system all the necessary subscripts could be put back in. Thus, the kind of ambiguity we are dealing with here is not very serious.)

**Lean 4**

- [InformationSystems/ApproximableMappingsBetweenDomains/Approximable/ApproximableMap.lean](ApproximableMap.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Approximable/ext.lean](ext.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Approximable/singleton_funion_eq.lean](singleton_funion_eq.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Approximable/exists_rel_of_subset_image.lean](exists_rel_of_subset_image.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Approximable/toElement.lean](toElement.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Approximable/Basic.lean](Basic.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Approximable/toElement_mono.lean](toElement_mono.lean)
- [InformationSystems/ApproximableMappingsBetweenDomains/Approximable.lean](../Approximable.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/Basic.lean](../../DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/Basic.lean)
