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

- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_approxMap_toElement.lean](element_toApproxMap_approxMap_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/fstMap_pairElements.lean](fstMap_pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_comm_β.lean](funion_comm_β.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/funion_self.lean](funion_self.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/liftLeft_funion.lean](liftLeft_funion.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/liftPair.lean](liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/ProdCon_liftPair.lean](ProdCon_liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/fstFinset_liftPair.lean](fstFinset_liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/liftRight_funion.lean](liftRight_funion.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_approxMap_toElement.lean](mem_approxMap_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_fst_of_subset_pairElements.lean](mem_fst_of_subset_pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken_eq.lean](mkFunToken_eq.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_element_toApproxMap.lean](approxMap_toElement_element_toApproxMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken_property.lean](mkFunToken_property.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mkFunToken.lean](mkFunToken.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap.lean](applyMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_empty_rel.lean](element_toApproxMap_empty_rel.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_mono.lean](element_toApproxMap_mono.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_rel_cod.lean](element_toApproxMap_rel_cod.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_rel_dom.lean](element_toApproxMap_rel_dom.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap_union_right.lean](element_toApproxMap_union_right.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/element_toApproxMap.lean](element_toApproxMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/pairElements.lean](pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_input_output_union.lean](rel_input_output_union.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_closed.lean](approxMap_toElement_closed.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_approxMap.lean](funCon_of_approxMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement_consistent.lean](approxMap_toElement_consistent.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/approxMap_toElement.lean](approxMap_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/sndFinset_liftPair.lean](sndFinset_liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/entSet_liftPair.lean](entSet_liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/rel_of_funTokens.lean](rel_of_funTokens.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/funCon_of_curry_pointwise.lean](funCon_of_curry_pointwise.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap.lean](curryMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/sndMap_pairElements.lean](sndMap_pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/mem_snd_of_subset_pairElements.lean](mem_snd_of_subset_pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftLeft.lean](subset_pairElements_liftLeft.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftRight.lean](subset_pairElements_liftRight.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/subset_pairElements_liftPair.lean](subset_pairElements_liftPair.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/applyMap_toElement.lean](applyMap_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/theorem_7_2.lean](theorem_7_2.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurryMap.lean](uncurryMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/Basic.lean](Basic.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/uncurry_curryMap.lean](uncurry_curryMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72/curryMap_unique.lean](curryMap_unique.lean)
- [InformationSystems/FunctionSpaceAsADomain/Theorem72.lean](../Theorem72.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/BoolPoint.lean](../Factoid75/BoolPoint.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/BoolToken.lean](../Factoid75/BoolToken.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/EmptyEntails.lean](../Factoid75/EmptyEntails.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/IsStrict.lean](../Factoid75/IsStrict.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictToken.lean](../Factoid75/StrictToken.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunToken.lean](../Factoid75/StrictFunToken.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/BasicInst22.lean](../Factoid75/BasicInst22.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/boolSat.lean](../Factoid75/boolSat.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/boolSat_bot.lean](../Factoid75/boolSat_bot.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/boolSat_sing.lean](../Factoid75/boolSat_sing.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/boolSystem.lean](../Factoid75/boolSystem.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/boolCon_trichotomy.lean](../Factoid75/boolCon_trichotomy.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/boolFalse.lean](../Factoid75/boolFalse.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/boolTrue.lean](../Factoid75/boolTrue.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_empty.lean](../Factoid75/emptyEntails_empty.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_funion.lean](../Factoid75/emptyEntails_funion.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/emptyEntails_mem_botElement.lean](../Factoid75/emptyEntails_mem_botElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/entSet_singleton_fls_of_ent_fls.lean](../Factoid75/entSet_singleton_fls_of_ent_fls.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/entSet_singleton_tru_of_ent_tru.lean](../Factoid75/entSet_singleton_tru_of_ent_tru.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap_unique.lean](../Factoid75/condMap_unique.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/filter_ne_subset_of_subset_insert_strict.lean](../Factoid75/filter_ne_subset_of_subset_insert_strict.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/insert_filter_ne_strict.lean](../Factoid75/insert_filter_ne_strict.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/mem_botElement_emptyEntails.lean](../Factoid75/mem_botElement_emptyEntails.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/IsStrictToken_of_IsStrict.lean](../Factoid75/IsStrictToken_of_IsStrict.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/not_emptyEntails_singleton_fls.lean](../Factoid75/not_emptyEntails_singleton_fls.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/not_emptyEntails_singleton_tru.lean](../Factoid75/not_emptyEntails_singleton_tru.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/not_ent_empty_fls.lean](../Factoid75/not_ent_empty_fls.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/not_ent_empty_tru.lean](../Factoid75/not_ent_empty_tru.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/not_ent_fls_tru.lean](../Factoid75/not_ent_fls_tru.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap_toElement_boolFalse.lean](../Factoid75/condMap_toElement_boolFalse.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/not_ent_tru_fls.lean](../Factoid75/not_ent_tru_fls.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap_toElement_boolTrue.lean](../Factoid75/condMap_toElement_boolTrue.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap_pair_roundtrip.lean](../Factoid75/condMap_pair_roundtrip.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/conditional_iso.lean](../Factoid75/conditional_iso.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75.lean](../Factoid75.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/strictBot.lean](../Factoid75/strictBot.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/strictify.lean](../Factoid75/strictify.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/IsStrict_strictify.lean](../Factoid75/IsStrict_strictify.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/strictify_toElement_le.lean](../Factoid75/strictify_toElement_le.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/subset_of_entSet_mem.lean](../Factoid75/subset_of_entSet_mem.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/condMap.lean](../Factoid75/condMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/IsStrict_condMap.lean](../Factoid75/IsStrict_condMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/toFunFinset.lean](../Factoid75/toFunFinset.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunCon.lean](../Factoid75/StrictFunCon.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/StrictFunEnt.lean](../Factoid75/StrictFunEnt.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/mem_toFunFinset.lean](../Factoid75/mem_toFunFinset.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/toFunFinset_empty.lean](../Factoid75/toFunFinset_empty.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/toFunFinset_insert.lean](../Factoid75/toFunFinset_insert.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/toFunFinset_singleton.lean](../Factoid75/toFunFinset_singleton.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/toFunFinset_subset.lean](../Factoid75/toFunFinset_subset.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/strictFunctionSystem.lean](../Factoid75/strictFunctionSystem.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/approxMap_toStrictElement.lean](../Factoid75/approxMap_toStrictElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/condElement.lean](../Factoid75/condElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/strictifyElement.lean](../Factoid75/strictifyElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid75/Basic.lean](../Factoid75/Basic.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/compOpUncurry.lean](../Factoid76/compOpUncurry.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/compOp.lean](../Factoid76/compOp.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/compOpUncurry_toElement.lean](../Factoid76/compOpUncurry_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/compOp_uncurry.lean](../Factoid76/compOp_uncurry.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/constOp.lean](../Factoid76/constOp.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/constOp_uncurry.lean](../Factoid76/constOp_uncurry.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/pairMap_comp_fst_snd_toElement.lean](../Factoid76/pairMap_comp_fst_snd_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/compOp_toElement.lean](../Factoid76/compOp_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76.lean](../Factoid76.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/constOp_toElement.lean](../Factoid76/constOp_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/pairMap_toElement_pairElements.lean](../Factoid76/pairMap_toElement_pairElements.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOpUncurry.lean](../Factoid76/pairOpUncurry.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOp.lean](../Factoid76/pairOp.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/Basic.lean](../Factoid76/Basic.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOpUncurry_toElement.lean](../Factoid76/pairOpUncurry_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOp_uncurry.lean](../Factoid76/pairOp_uncurry.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid76/pairOp_toElement.lean](../Factoid76/pairOp_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/InfoSysObj.lean](../Factoid77/InfoSysObj.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp.lean](../Factoid77/acomp.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp_toElement.lean](../Factoid77/acomp_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp_assoc.lean](../Factoid77/acomp_assoc.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp_id.lean](../Factoid77/acomp_id.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/curry_uncurry.lean](../Factoid77/curry_uncurry.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/exp.lean](../Factoid77/exp.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/id_acomp.lean](../Factoid77/id_acomp.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/instCategoryInfoSysObj.lean](../Factoid77/instCategoryInfoSysObj.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/prod.lean](../Factoid77/prod.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/productLimitCone.lean](../Factoid77/productLimitCone.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap.lean](../Factoid77/swapMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp_swap_fst.lean](../Factoid77/acomp_swap_fst.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/acomp_swap_snd.lean](../Factoid77/acomp_swap_snd.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/swapMap_acomp_swapMap.lean](../Factoid77/swapMap_acomp_swapMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_fst_toElement.lean](../Factoid77/swap_fst_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/swap_snd_toElement.lean](../Factoid77/swap_snd_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/unit.lean](../Factoid77/unit.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/terminalLimitCone.lean](../Factoid77/terminalLimitCone.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/instCartesianMonoidalCategoryInfoSysObj.lean](../Factoid77/instCartesianMonoidalCategoryInfoSysObj.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/curryProduct.lean](../Factoid77/curryProduct.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_fst_toElement.lean](../Factoid77/lift_fst_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/lift_snd_toElement.lean](../Factoid77/lift_snd_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/pair_after_swap_toElement.lean](../Factoid77/pair_after_swap_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElement_eq_productElement.lean](../Factoid77/tensorElement_eq_productElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/prodElementToTensorElement.lean](../Factoid77/prodElementToTensorElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElementToProdElement.lean](../Factoid77/tensorElementToProdElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorElementToProdElement_prodElementToTensorElement.lean](../Factoid77/tensorElementToProdElement_prodElementToTensorElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHom_eq_productMap.lean](../Factoid77/tensorHom_eq_productMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/prodHomToTensorHom.lean](../Factoid77/prodHomToTensorHom.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/prodHomToTensorHom_toElement.lean](../Factoid77/prodHomToTensorHom_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorHomToProdHom.lean](../Factoid77/tensorHomToProdHom.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight.lean](../Factoid77/curryRight.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorMap_eq_productMap.lean](../Factoid77/tensorMap_eq_productMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/productMapToTensorMap.lean](../Factoid77/productMapToTensorMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/productMapToTensorMap_comp_toElement.lean](../Factoid77/productMapToTensorMap_comp_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorLeft_map_eq.lean](../Factoid77/tensorLeft_map_eq.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryProduct.lean](../Factoid77/uncurryProduct.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryRight.lean](../Factoid77/uncurryRight.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/curryRight_uncurryRight.lean](../Factoid77/curryRight_uncurryRight.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryRight_curryRight.lean](../Factoid77/uncurryRight_curryRight.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpEquiv.lean](../Factoid77/tensorExpEquiv.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryRight_toElement.lean](../Factoid77/uncurryRight_toElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/uncurryRight_comp_left.lean](../Factoid77/uncurryRight_comp_left.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpEquiv_natural.lean](../Factoid77/tensorExpEquiv_natural.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor.lean](../Factoid77/expFunctor.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorExpAdjunction.lean](../Factoid77/tensorExpAdjunction.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/Basic.lean](../Factoid77/Basic.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/expFunctor_obj.lean](../Factoid77/expFunctor_obj.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/ihom_obj_eq_exp.lean](../Factoid77/ihom_obj_eq_exp.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77.lean](../Factoid77.lean)
- [InformationSystems/FunctionSpaceAsADomain/Factoid77/tensorObj_eq_prod.lean](../Factoid77/tensorObj_eq_prod.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixChain.lean](../Fixpoint/FixChain.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/FixReach.lean](../Fixpoint/FixReach.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_con.lean](../Fixpoint/fixChain_con.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_empty.lean](../Fixpoint/fixChain_empty.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_mono_w.lean](../Fixpoint/fixChain_mono_w.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_pad_front.lean](../Fixpoint/fixChain_pad_front.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_pad.lean](../Fixpoint/fixChain_pad.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_con.lean](../Fixpoint/fixReach_con.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_empty.lean](../Fixpoint/fixReach_empty.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_mono_w.lean](../Fixpoint/fixReach_mono_w.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/funEnt_union_step.lean](../Fixpoint/funEnt_union_step.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_union.lean](../Fixpoint/fixChain_union.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixReach_union.lean](../Fixpoint/fixReach_union.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap.lean](../Fixpoint/fixMap.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement.lean](../Fixpoint/fixElement.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/Basic.lean](../Fixpoint/Basic.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_step_of_rel.lean](../Fixpoint/fixChain_step_of_rel.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixChain_subset_pre_fixed.lean](../Fixpoint/fixChain_subset_pre_fixed.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_le_of_pre_fixed.lean](../Fixpoint/fixElement_le_of_pre_fixed.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/toElement_fixElement_le.lean](../Fixpoint/toElement_fixElement_le.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_fixed.lean](../Fixpoint/fixElement_fixed.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixElement_unique.lean](../Fixpoint/fixElement_unique.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint/fixMap_unique.lean](../Fixpoint/fixMap_unique.lean)
- [InformationSystems/FunctionSpaceAsADomain/Fixpoint.lean](../Fixpoint.lean)
