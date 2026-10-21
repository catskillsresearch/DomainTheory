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

- [Definition 3.1](1982_Definition_3_1.md)

**Lean 4**

- [InformationSystems/ElementsOfASystem/Factoid32.lean](Factoid32.lean)
- [InformationSystems/ElementsOfASystem/Factoid32/Basic.lean](Factoid32/Basic.lean)
- [InformationSystems/ElementsOfASystem/Factoid32/factoid_3_2.lean](Factoid32/factoid_3_2.lean)
- [InformationSystems/ElementsOfASystem/Factoid33.lean](Factoid33.lean)
- [InformationSystems/ElementsOfASystem/Factoid33/Basic.lean](Factoid33/Basic.lean)
- [InformationSystems/ElementsOfASystem/Factoid33/botElement.lean](Factoid33/botElement.lean)
- [InformationSystems/ElementsOfASystem/Factoid33/botElement_le.lean](Factoid33/botElement_le.lean)
- [InformationSystems/ElementsOfASystem/Factoid34.lean](Factoid34.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/AllConsistent.lean](Factoid34/AllConsistent.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/Basic.lean](Factoid34/Basic.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/IsTotal.lean](Factoid34/IsTotal.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/eq_of_carrier_univ_of_isTotal.lean](Factoid34/eq_of_carrier_univ_of_isTotal.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/eq_topElement_of_isTotal.lean](Factoid34/eq_topElement_of_isTotal.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/exists_top_iff_allConsistent.lean](Factoid34/exists_top_iff_allConsistent.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/exists_unique_total_of_allConsistent.lean](Factoid34/exists_unique_total_of_allConsistent.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/isTotal_iff_eq_topElement.lean](Factoid34/isTotal_iff_eq_topElement.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/isTotal_of_carrier_univ.lean](Factoid34/isTotal_of_carrier_univ.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/le_topElement.lean](Factoid34/le_topElement.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/topElement.lean](Factoid34/topElement.lean)
- [InformationSystems/ElementsOfASystem/Factoid34/topElement_isTotal.lean](Factoid34/topElement_isTotal.lean)
- [InformationSystems/ElementsOfASystem/Factoid35.lean](Factoid35.lean)
- [InformationSystems/ElementsOfASystem/Factoid35/Basic.lean](Factoid35/Basic.lean)
- [InformationSystems/ElementsOfASystem/Factoid35/closure.lean](Factoid35/closure.lean)
- [InformationSystems/ElementsOfASystem/Factoid35/mem_closure_iff.lean](Factoid35/mem_closure_iff.lean)
- [InformationSystems/ElementsOfASystem/Factoid35/subset_closure.lean](Factoid35/subset_closure.lean)
- [InformationSystems/ElementsOfASystem/Factoid36.lean](Factoid36.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/Basic.lean](Factoid36/Basic.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/approxUnion.lean](Factoid36/approxUnion.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/closure_le_element.lean](Factoid36/closure_le_element.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/closure_le_of_entSet.lean](Factoid36/closure_le_of_entSet.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/closure_le_of_subset.lean](Factoid36/closure_le_of_subset.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/closures_directed.lean](Factoid36/closures_directed.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/element_eq_approxUnion.lean](Factoid36/element_eq_approxUnion.lean)
- [InformationSystems/ElementsOfASystem/Factoid36/mem_element_iff_mem_closure.lean](Factoid36/mem_element_iff_mem_closure.lean)
- [InformationSystems/InformationSystems/InfoSys/Element.lean](../InformationSystems/InfoSys/Element.lean)
