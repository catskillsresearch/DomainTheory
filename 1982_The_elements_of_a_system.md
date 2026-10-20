# The elements of a system

Let $\mathbf{A}$ be an information system, and suppose we already had a concept of being an element of $\mathbf{A}$. The data objects are meant to be propositions about elements, so if $X$ is in $D_{\mathbf{A}}$ and if $x$ is an element, then we can be expected to know what it means to say that $X$ is true of $x$. Since all we are given is the set of data objects $D_{\mathbf{A}}$, we have to assume that it contains enough objects to distinguish between distinct elements. (If there were not enough of them, we would have to change the set $D_{\mathbf{A}}$.) Formally, we can write of two elements $x$ and $y$:

$$
x = y \quad \text{iff all } X \in D_{\mathbf{A}} \text{ which are true of } x \text{ are also true of } y, \text{ and conversely.}
$$

If this principle is accepted, then the elements can be *identified* with the sets of propositions true of them; formally we can assert:

$$
x = \{X \in D_{\mathbf{A}} \mid X \text{ is true of } x\}.
$$

There can be no confusion injected here in identifying elements that ought to be distinct, since we are assuming that there are enough data objects in the system. If for some reason we felt we ought to have more of them to distinguish between more elements, then we would have to pass to a larger and *different* information system. By agreement, then, the above equation is a tautology.
So, for the sake of simplicity, elements can be taken to be *sets* of data objects. But, we hasten to ask, which sets? The question is really: What are the properties of truth? The answers are well known, and, in fact, we have already used them in our examples in the last section. In words, the set of true propositions about a possible element must be (i) consistent in itself, and (ii) closed under entailment (or *deductively closed*, for short). Condition (i) is clear because we are talking about a *possible* element, not an impossible one. Condition (ii) is acceptable, because, by the very meaning of the word, entailment should be truth preserving. In addition, we are also saying the converse: *any* set having properties (i) and (ii) corresponds to a (partial) element. Here is the formal statement:

**DEFINITION 3.1.** The *elements* of the information system $\mathbf{A} = (D_{\mathbf{A}}, \Delta_{\mathbf{A}}, \mathrm{Con}_{\mathbf{A}}, \vdash_{\mathbf{A}})$ are those subsets $x$ of $D_{\mathbf{A}}$ where:

(i) all finite subsets of $x$ are in $\mathrm{Con}_{\mathbf{A}}$; and

(ii) whenever $u \subseteq x$ and $u \vdash_{\mathbf{A}} X$, then $X \in x$.

We write $x \in |\mathbf{A}|$ to mean $x$ is an element of the system. This set of elements is the *domain* determined by the given system. An element that is not included in any strictly larger element in the domain is called a *total element*; the set of total elements is denoted by $\mathrm{Tot}_{\mathbf{A}}$. ■

*Remarks.* Any subset of $D_{\mathbf{A}}$ satisfying 3.1 (i) can be called consistent, and every consistent set generates an element by closing it under entailment. Note, too, that every element contains $\Delta_{\mathbf{A}}$ as a member, because the least informative proposition is true of all elements. Moreover, every domain has a least element contained in all other elements. We call it $\bot_{\mathbf{A}}$ and write formally:

$$\bot_{\mathbf{A}} = \{X \in D_{\mathbf{A}} \mid \{\Delta_{\mathbf{A}}\} \vdash_{\mathbf{A}} X\}.$$

In the above we could just as well have used the empty set $\emptyset$ in place of $\{\Delta_{\mathbf{A}}\}$; and often we can write simply $\vdash_{\mathbf{A}} X$.

The element $\bot_{\mathbf{A}}$ is often called the *bottom* element of the domain. There need be no *top* or maximal element, $\top_{\mathbf{A}}$. Such an element is possible if, and only if, *all* finite subsets of $D_{\mathbf{A}}$ are consistent, in which case, as a set, $\top_{\mathbf{A}} = D_{\mathbf{A}}$. The possibility is not excluded—rather, it is not required. In case $\top_{\mathbf{A}}$ exists, it is the unique total element of the domain, and conversely. ■

Returning to our question of the balance between axiomatizaton and construction, what we have done is first to axiomatize the properties of $(D_{\mathbf{A}}, \Delta_{\mathbf{A}}, \mathrm{Con}_{\mathbf{A}}, \vdash_{\mathbf{A}})$, then to construct the domain $|\mathbf{A}|$ from this structure. The principal claimed advantages are that the axioms for consistency and entailment are already essentially familiar, and that the definition of elementhood is direct and natural from our understanding of the properties of truth.

*The examples.* Let us look again at the three examples of information systems of the last section. (1) In the first we see that the elements, by the formal definition, are either the finite sets $\{n \mid n \leq m\}$ or the whole set (i.e. $\top$). Intuitively, this corresponds to the fact that the chosen propositions only give *lower bounds* on a possible element; thus, no element is “finished” until it becomes infinite. (2) In the second example there is no top, and the elements are the sets of the form:

$$\{(n, q) \mid n \leq m \leq p \leq q\},$$
where $m \leq p$ are given, and where $q = \infty$ is allowed. The total elements here correspond to the (non-negative) integers, and the partial elements to situations where the lower and upper bounds have not come exactly together. (3) In the third example, the elements are just the graphs (i.e. sets of ordered pairs) of partial functions from $A$ into $B$ (with the object $\Delta$ adjoined to the graph). Total elements correspond to total functions (i.e. functions well defined on all of the set $A$). ■

The reader should be able to obtain some more examples of information systems from his own experience and should then consider what the corresponding domain is like. Examples are really quite easy to make up. Needless to say, Mathematical Logic provides a host of information systems, but logicians do not often consider the domains determined by the the systems they know to be worthy of study *in themselves*. In particular, it does not seem to be widely recognized that the domains obtained from information systems form a rich category, as we shall show later. The word "category" is definitely being used here in the precise technical sense of Category Theory, and the application of the notion is very appropriate since the category of domains has very good closure properties.

**Lean 4**

- [InformationSystems/ElementsOfASystem/Factoid32.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid32.lean)
- [InformationSystems/ElementsOfASystem/Factoid32/Basic.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid32/Basic.lean)
- [InformationSystems/ElementsOfASystem/Factoid32/factoid_3_2.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid32/factoid_3_2.lean)
- [InformationSystems/ElementsOfASystem/Factoid33.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid33.lean)
- [InformationSystems/ElementsOfASystem/Factoid33/Basic.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid33/Basic.lean)
- [InformationSystems/ElementsOfASystem/Factoid33/botElement.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid33/botElement.lean)
- [InformationSystems/ElementsOfASystem/Factoid33/botElement_le.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid33/botElement_le.lean)
- [InformationSystems/ElementsOfASystem/Factoid34.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/AllConsistent.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/AllConsistent.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/Basic.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/Basic.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/IsTotal.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/IsTotal.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/eq_of_carrier_univ_of_isTotal.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/eq_of_carrier_univ_of_isTotal.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/eq_topElement_of_isTotal.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/eq_topElement_of_isTotal.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/exists_top_iff_allConsistent.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/exists_top_iff_allConsistent.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/exists_unique_total_of_allConsistent.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/exists_unique_total_of_allConsistent.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/isTotal_iff_eq_topElement.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/isTotal_iff_eq_topElement.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/isTotal_of_carrier_univ.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/isTotal_of_carrier_univ.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/le_topElement.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/le_topElement.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/topElement.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/topElement.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/topElement_isTotal.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid34/topElement_isTotal.lean)
- [InformationSystems/ElementsOfASystem/Factoid35.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid35.lean)
- [InformationSystems/ElementsOfASystem/Factoid35/Basic.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid35/Basic.lean)
- [InformationSystems/ElementsOfASystem/Factoid35/closure.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid35/closure.lean)
- [InformationSystems/ElementsOfASystem/Factoid35/mem_closure_iff.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid35/mem_closure_iff.lean)
- [InformationSystems/ElementsOfASystem/Factoid35/subset_closure.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid35/subset_closure.lean)
- [InformationSystems/ElementsOfASystem/Factoid36.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid36.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/Basic.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid36/Basic.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/approxUnion.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid36/approxUnion.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/closure_le_element.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid36/closure_le_element.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/closure_le_of_entSet.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid36/closure_le_of_entSet.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/closure_le_of_subset.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid36/closure_le_of_subset.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/closures_directed.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid36/closures_directed.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/element_eq_approxUnion.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid36/element_eq_approxUnion.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/mem_element_iff_mem_closure.lean](DomainTheory/InformationSystems/ElementsOfASystem/Factoid36/mem_element_iff_mem_closure.lean)
- [InformationSystems/InformationSystems/InfoSys/Element.lean](DomainTheory/InformationSystems/InformationSystems/InfoSys/Element.lean)
