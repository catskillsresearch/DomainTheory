# Theorem 7.2

**THEOREM 7.2.** If $\mathbf{A}$, $\mathbf{B}$, and $\mathbf{C}$ are information systems, then so is $\mathbf{A} \to \mathbf{B}$, and the approximable mappings $f : \mathbf{A} \to \mathbf{B}$ are exactly the elements $f \in |\mathbf{A} \to \mathbf{B}|$. Moreover we have an approximable mapping $\text{apply} : (\mathbf{B} \to \mathbf{C}) \times \mathbf{B} \to \mathbf{C}$ such that whenever $g : \mathbf{B} \to \mathbf{C}$ and $y \in |\mathbf{B}|$, then

$$\text{apply}(g, y) = g(y).$$

Furthermore, for all approximable mappings $h : \mathbf{A} \times \mathbf{B} \to \mathbf{C}$, there is one and only one approximable mapping $\text{curry } h : \mathbf{A} \to (\mathbf{B} \to \mathbf{C})$ such that

$$h = \text{apply} \circ \langle (\text{curry } h) \circ \text{fst}, \text{snd} \rangle.$$

*Proof.* We have already remarked on the essentials of the proof above. Definition 7.1 was devised to characterize exactly in $\mathrm{Con}_{\mathbf{A} \to \mathbf{B}}$ the finite subsets of approximable functions, which, as binary relations, are being regarded as sets of ordered pairs. If $f : \mathbf{A} \to \mathbf{B}$ and if $w \subseteq f$, then from the properties of approximable functions, it can be checked directly that $w$ satisfies the right-hand side of 7.1(iii). Conversely, if $w \in \mathrm{Con}_{\mathbf{A} \to \mathbf{B}}$, then, as we have said, the relation which is defined by 7.1(iv) and may be notated by:

$$\overline{w} = \{ (u', v') \mid w \vdash_{\mathbf{A} \to \mathbf{B}} (u', v') \},$$

is an approximable mapping, as can be proved using the right-hand side of 7.1(iv) and the usual properties of $\vdash_{\mathbf{A}}$ and $\vdash_{\mathbf{B}}$. Since $w \subseteq \overline{w}$, we see that $w \vdash_{\mathbf{A} \to \mathbf{B}} w'$ if, and only if, for all approximable $f : \mathbf{A} \to \mathbf{B}$, $w \subseteq f$ implies $w' \subseteq f$. (This is also the same as $w' \subseteq \overline{w}$, of course.) From these considerations it follows that not only is $\mathbf{A} \to \mathbf{B}$ an information system, but all approximable mappings are elements. Finally, if $f \in |\mathbf{A} \to \mathbf{B}|$, then—as a binary relation—it must be an approximable mapping, because the properties of Definition 5.1 are built into 7.1.

The construction of the special mapping $\text{apply}$ as an approximable mapping also uses the idea of 7.1(iv). The consistent sets of the compound space $(\mathbf{B} \to \mathbf{C}) \times \mathbf{B}$ are essentially pairs of consistent sets, say $w \in \mathrm{Con}_{\mathbf{B} \to \mathbf{C}}$ and $u' \in \mathrm{Con}_{\mathbf{B}}$. Now the relation we want from such pairs to consistent sets $v' \in \mathrm{Con}_{\mathbf{C}}$ is just nothing more or less than $w \vdash_{\mathbf{B} \to \mathbf{C}} (u', v')$. Our discussion in the previous paragraph hints at why $\text{apply}$ does in fact reproduce functional application when we evaluate $\text{apply}(g, y)$.

The definition of $\text{curry } h$ uses the same trick of regarding a binary relation with one term in a relationship being a pair as corresponding to another relation with one coordinate of the pair shifted to the other side. Specifically, we can think of an approximable mapping $h : \mathbf{A} \times \mathbf{B} \to \mathbf{C}$ as a relation from pairs $(u, v)$ of consistent sets for $\mathbf{A}$ and $\mathbf{B}$, respectively, over to consistent sets $w$ for $\mathbf{C}$. What we want for $\text{curry } h$ is the relationship that goes from $u$ to the pair $(v, w)$. Of course $(v, w)$ is just one data object for $\mathbf{B} \to \mathbf{C}$, but the input/output passage from the consistent sets of $\mathbf{A}$ to these objects is sufficient to determine $\text{curry } h$ as an approximable mapping. The exact connection between the two mappings is given in terms of function values as follows:

$$h(x, y) = (\text{curry } h)(x)(y),$$

for all $x \in |\mathbf{A}|$ and $y \in |\mathbf{B}|$. From this equation it follows that $\text{curry } h$ is uniquely determined. But, from what we know about $\text{apply}$, this is actually the same equation as that stated at the end of the theorem. $\blacksquare$
*Approximations to functions.* Why have approximable functions been given this name? In general, elements of domains are the limits of their finite approximations. We have just indicated why the approximable mappings from one domain into another do form the elements of a domain themselves. We have explicitly shown how to construct the finite approximable mappings $\overline{w}$. A closer examination of the definitions would emphasize the very constructive nature of this analysis. It follows that the approximable mappings can therefore be approximated by simple functions. It does not follow that all approximable mappings are simple or constructive, since what takes place in the limiting process can be very complex. But the result does show how we can start to make distinctions once a precise sense of approximation is uncovered. $\blacksquare$

*Higher-type functions and the combinators.* In the above discussion we have already combined the function-space construction with other domains by means of products. But there is nothing now stopping us from iterating the arrow domain constructor with itself as much as we like. This is how the so-called higher types are formed. In certain categories, such as the category of sets, this is a non-constructive move leading to the higher cardinal numbers. In the category of domains, however, the construct is constructive, because we have shown how to define all the parts of $\mathbf{A} \to \mathbf{B}$ in terms of very finite data objects (assuming, it need hardly be added, that $\mathbf{A}$ and $\mathbf{B}$ are constructively given).

Once the higher types have been formed as spaces, it must be asked what we are to do with them. The answer is that there are many, many mappings between these spaces that can be defined in terms of the simple notions we have been working with. These mappings are useful for the following reason: the higher types provide remarkable scope for modelling notions (as those needed in denotational semantics for example), but the various aspects of the models have to be related—and this is where these mappings come into play. We have already seen a preliminary example in the last theorem, which can be interpreted as saying why the two domains shown are isomorphic:

$$\mathbf{A} \times \mathbf{B} \to \mathbf{C} \cong \mathbf{A} \to (\mathbf{B} \to \mathbf{C}).$$

We have neither the time nor the space to present a full theory of higher-type operators here, so some further examples will have to suffice. First, we have already made use of constant mappings. Since the construction of them is very uniform, there ought to be an associated operator. In fact, we have already been using it notationally. We have the approximable mapping $\text{const} : \mathbf{B} \to (\mathbf{A} \to \mathbf{B})$ that takes every element of $\mathbf{B}$ to the corresponding constant function. (It has to be checked that this is an approximable mapping.) Note that there is a different mapping for each pair of domains $\mathbf{A}$ and $\mathbf{B}$, because the resulting types of $\text{const}$ are different.

As another example, take the pairing of functions explained in Proposition 6.2. We can think of the operator in this case being

$$\text{pair} : (\mathbf{C} \to \mathbf{A}) \times (\mathbf{C} \to \mathbf{B}) \to (\mathbf{C} \to (\mathbf{A} \times \mathbf{B})),$$

where for functions of the proper type we have:

$$\text{pair}(f, g) = \langle f, g \rangle$$

There will be a similar operator for the construct of Proposition 6.4.
Of course the most basic operator of function composition is also approximable of the appropriate type. We can write:

$$\mathrm{comp} : (\mathbf{B} \to \mathbf{C}) \times (\mathbf{A} \to \mathbf{B}) \to (\mathbf{A} \to \mathbf{C}),$$

where for functions of the right types we have:

$$\mathrm{comp}(g, f) = g \circ f.$$

The approximability has to be checked, of course. But once a number of the more primitive operators have been established as being approximable, then others can be proved to be so by writing them as combinations of previously obtained operators. $\blacksquare$

*Categories again.* All of what we have been saying about operators ties in with category theory very nicely—as the category theorists have known for a long time. The technical term for what we have been doing in part is cartesian closed category—that is a property of the category of domains. Without going into details, that is essentially what 6.2 and 7.2 show of our category. But domains have many other properties beyond being a cartesian closed category. For example the possibility of forming sums is an extra (and useful) bonus, and there are many others. Nevertheless, the categorical viewpoint is a good way of organizing the properties, and it suggests other things to look for from our experiences with other categories. The next result gives a particularly important notion that can be expressed as an operator. $\blacksquare$

**Lean 4**

- [InformationSystems/FunctionSpaceAsADomain/Theorem72.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/Basic.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/Basic.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/ProdCon_liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/ProdCon_liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_closed.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_closed.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_consistent.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_consistent.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_element_toApproxMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_element_toApproxMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap_unique.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap_unique.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_approxMap_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_approxMap_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_empty_rel.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_empty_rel.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_mono.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_mono.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_rel_cod.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_rel_cod.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_rel_dom.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_rel_dom.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_union_right.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_union_right.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/entSet_liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/entSet_liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/fstFinset_liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/fstFinset_liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/fstMap_pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/fstMap_pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_approxMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_approxMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_curry_pointwise.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_curry_pointwise.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_comm_β.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_comm_β.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_self.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_self.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/liftLeft_funion.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/liftLeft_funion.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/liftRight_funion.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/liftRight_funion.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_approxMap_toElement.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_approxMap_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_fst_of_subset_pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_fst_of_subset_pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_snd_of_subset_pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_snd_of_subset_pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken_eq.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken_eq.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken_property.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken_property.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_input_output_union.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_input_output_union.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_of_funTokens.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_of_funTokens.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/sndFinset_liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/sndFinset_liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/sndMap_pairElements.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/sndMap_pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftLeft.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftLeft.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftPair.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftRight.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftRight.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/theorem_7_2.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/theorem_7_2.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurryMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurryMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurry_curryMap.lean](DomainTheory/InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurry_curryMap.lean)
