# Products and sums of domains

In the category of sets, the product (the cartesian product) of two sets is by definition just the set of ordered pairs of elements. We could use the same definition in the category of domains—provided we worked in terms of the elements of the domains. The disadvantage is that the determination of the product domain from data objects is lost, or at least pushed into the background. We shall therefore give a construction of products directly in terms of the given data objects, and then show how to prove that the product is just the one expected when we look at the elements.

The idea for the definition is a simple one. Think of two domains $\mathbf{A}$ and $\mathbf{B}$. A data object $X \in D_{\mathbf{A}}$ can be giving information about a possible element $x \in |\mathbf{A}|$, and a data object $Y \in D_{\mathbf{B}}$ can be giving information about a possible element $y \in |\mathbf{B}|$. How do we wish to give information about the pair $(x, y)$? The first piece of advice is not to say all that is known all at once. For
example, if pressed, we can say we know $X$ about the first coordinate of the pair; only later, if really pressed, we can say we also know $Y$ about the second coordinate. The point is that data objects provide only partial information, and it does not matter if it takes several of them to give fairly complete information about the whole element. This attitude motivates, then, the particular form of our official definition.

**DEFINITION 6.1.** Let $\mathbf{A}$ and $\mathbf{B}$ be two information systems. By $\mathbf{A} \times \mathbf{B}$, the *product system*, we understand the system where:

(i) $D_{\mathbf{A} \times \mathbf{B}} = \{(X, \Delta_{\mathbf{B}}) \mid X \in D_{\mathbf{A}}\} \cup \{(\Delta_{\mathbf{A}}, Y) \mid Y \in D_{\mathbf{B}}\}$;

(ii) $\Delta_{\mathbf{A} \times \mathbf{B}} = (\Delta_{\mathbf{A}}, \Delta_{\mathbf{B}})$;

(iii) $u \in \mathrm{Con}_{\mathbf{A} \times \mathbf{B}}$ iff $\mathrm{fst}\, u \in \mathrm{Con}_{\mathbf{A}}$ and $\mathrm{snd}\, u \in \mathrm{Con}_{\mathbf{B}}$;

(iv') $u \vdash_{\mathbf{A} \times \mathbf{B}} (X', \Delta_{\mathbf{B}})$ iff $\mathrm{fst}\, u \vdash_{\mathbf{A}} X'$; and

(iv'') $u \vdash_{\mathbf{A} \times \mathbf{B}} (\Delta_{\mathbf{A}}, Y')$ iff $\mathrm{snd}\, u \vdash_{\mathbf{B}} Y'$;

where, in (iii), $u$ is any finite subset of $D_{\mathbf{A} \times \mathbf{B}}$, in (iv') and (iv''), $u \in \mathrm{Con}_{\mathbf{A} \times \mathbf{B}}$, and we let:

$$\mathrm{fst}\, u = \{X \in D_{\mathbf{A}} \mid (X, \Delta_{\mathbf{B}}) \in u\}, \text{ and}$$

$$\mathrm{snd}\, u = \{Y \in D_{\mathbf{B}} \mid (\Delta_{\mathbf{A}}, Y) \in u\}. \quad \blacksquare$$

Note that in 6.1(i) the two sets in the union are just two copies of $D_{\mathbf{A}}$ and $D_{\mathbf{B}}$, respectively. There is a shared member, however, the object $(\Delta_{\mathbf{A}}, \Delta_{\mathbf{B}})$, which is indeed the least informative data object—whether it is looked at from the point of view of $\mathbf{A}$ or of $\mathbf{B}$. We could have used all the pairs $(X, Y)$, but if we did, the consistent set $\{(X, Y)\}$ would be deductively equivalent to the set $\{(X, \Delta_{\mathbf{B}}), (\Delta_{\mathbf{A}}, Y)\}$ according to the definition of $\vdash_{\mathbf{A} \times \mathbf{B}}$, and so there is not much point in having this redundancy. Strictly speaking, we should not make these remarks until we have actually verified that 6.1 is indeed a proper definition.

**PROPOSITION 6.2.** *If $\mathbf{A}$ and $\mathbf{B}$ are information systems, then so is $\mathbf{A} \times \mathbf{B}$, and we have mappings*

$$\mathrm{fst} : \mathbf{A} \times \mathbf{B} \to \mathbf{A} \text{ and } \mathrm{snd} : \mathbf{A} \times \mathbf{B} \to \mathbf{B},$$

*such that, for approximable mappings*

$$f : \mathbf{C} \to \mathbf{A} \text{ and } g : \mathbf{C} \to \mathbf{B},$$

*there is one and only one approximable mapping $\langle f, g \rangle : \mathbf{C} \to \mathbf{A} \times \mathbf{B}$ such that*

$$\mathrm{fst} \circ \langle f, g \rangle = f \text{ and } \mathrm{snd} \circ \langle f, g \rangle = g.$$

*Proof.* Checking that 6.1 does indeed define an information system is straightforward, but there are six things that must be proved according to Definition 2.1. We have to leave the details to the reader. Next using the notation of 6.1, where $\mathrm{fst}$ and $\mathrm{snd}$ were applied as operations on consistent sets $u \in \mathrm{Con}_{\mathbf{A} \times \mathbf{B}}$, we redefine matters to have approximable mappings, where, for $v \in \mathrm{Con}_{\mathbf{A}}$ and $w \in \mathrm{Con}_{\mathbf{B}}$,
$(1)$ $u\ \mathrm{fst}\ v$ iff $\mathrm{fst}\, u \vdash_{\mathbf{A}} v$;

$(2)$ $u\ \mathrm{snd}\ w$ iff $\mathrm{snd}\, u \vdash_{\mathbf{B}} w$; and

$(3)$ $s\ \langle f, g \rangle\ u$ iff $s\ f\ (\mathrm{fst}\, u)$ and $s\ g\ (\mathrm{snd}\, u)$.

Because we defined $\mathbf{A} \times \mathbf{B}$ so that consistency and entailment worked independently on the two halves of the set of data objects, it is easy to check that (1)–(3) define approximable mappings having the desired properties.

The uniqueness of $\langle f, g \rangle$ comes out of the observation that, if $z$ and $z'$ are two elements of $\mathbf{A} \times \mathbf{B}$ for which

$$\mathrm{fst}(z) = \mathrm{fst}(z') \text{ and } \mathrm{snd}(z) = \mathrm{snd}(z'),$$

then $z = z'$. The reason is that $\mathrm{fst}$ and $\mathrm{snd}$ just divide elements into the two kinds of data objects, and then strip off the parentheses. (Look back at Definition 6.1.) No information is lost, so if $z$ and $z'$ are transformed into the same elements both times, then they have to be the same.

That lemma treats one pair of elements at a time, but $\langle f, g \rangle$ is a function. But if $\langle f, g \rangle'$ were another function satisfying the conditions of the above proposition, then the two functions would be pointwise equal. We could then quote 5.3 to assure ourselves that they are the same function. $\blacksquare$

*Ordered pairs.* By using the definition

$$(x, y) = \langle \mathrm{const}(x), \mathrm{const}(y) \rangle (\bot_{\mathbf{C}}),$$

which invokes 6.2 on any convenient fixed domain $\mathbf{C}$, it is easy to prove that $|\mathbf{A} \times \mathbf{B}|$ is in a one-one correspondence with the set-theoretical product of $|\mathbf{A}|$ and $|\mathbf{B}|$. Indeed, it can be shown that for $x \in |\mathbf{A}|$ and $y \in |\mathbf{B}|$,

$(1)$ $(x, y) = \{(X, \Delta_{\mathbf{B}}) \mid X \in x\} \cup \{(\Delta_{\mathbf{A}}, Y) \mid Y \in y\} \in |\mathbf{A} \times \mathbf{B}|$;

$(2)$ $\mathrm{fst}(x, y) = x$;

$(3)$ $\mathrm{snd}(x, y) = y$;

and, for all $z \in |\mathbf{A} \times \mathbf{B}|$,

$(4)$ $z = (\mathrm{fst}\, z, \mathrm{snd}\, z)$.

Also, using the notation of 6.2, we can say that

$(5)$ $\langle f, g \rangle(t) = (f(t), g(t))$,

for all $t \in |\mathbf{C}|$.

There are also remarks that could be made about the pointwise nature of the partial ordering of $|\mathbf{A} \times \mathbf{B}|$, but we will not formulate them here. We do remark, however, that there is also a trivial product of no terms, $\mathbf{1}$, called the *unit type* or *domain*. It is such that $D_{\mathbf{1}} = \{\Delta_{\mathbf{1}}\}$, and
that equation determines it up to isomorphism. The domain $\mathbf{1}$ has but one element, namely $\perp_{\mathbf{1}}$. Note also that all approximable mappings $f : \mathbf{1} \to \mathbf{A}$ are constant, which shows how Definition 5.1 is a generalization of Definition 3.1. Note finally that there is but one approximable mapping $f : \mathbf{A} \to \mathbf{1}$, namely $f = 0 = \mathrm{const}(\perp_{\mathbf{1}})$. $\blacksquare$

We turn now to the definition and properties of sums of domains.

**DEFINITION 6.3.** Let $\mathbf{A}$ and $\mathbf{B}$ be two information systems. By $\mathbf{A} + \mathbf{B}$, the *separated sum system*, we understand the system where, after choosing some convenient object $\Delta$ belonging neither to $D_{\mathbf{A}}$ nor to $D_{\mathbf{B}}$, we have:

(i) $D_{\mathbf{A}+\mathbf{B}} = \{(X, \Delta) \mid X \in D_{\mathbf{A}}\} \cup \{(\Delta, Y) \mid Y \in D_{\mathbf{B}}\} \cup \{(\Delta, \Delta)\}$;

(ii) $\Delta_{\mathbf{A}+\mathbf{B}} = (\Delta, \Delta)$;

(iii) $u \in \mathrm{Con}_{\mathbf{A}+\mathbf{B}}$ iff either $\mathrm{lft}\, u \in \mathrm{Con}_{\mathbf{A}}$ and $\mathrm{rht}\, u = \emptyset$ or $\mathrm{lft}\, u = \emptyset$ and $\mathrm{rht}\, u \in \mathrm{Con}_{\mathbf{B}}$;

(iv') $u \vdash_{\mathbf{A}+\mathbf{B}} (X', \Delta)$ iff $\mathrm{lft}\, u \neq \emptyset$ and $\mathrm{lft}\, u \vdash_{\mathbf{A}} X'$;

(iv'') $u \vdash_{\mathbf{A}+\mathbf{B}} (\Delta, Y')$ iff $\mathrm{rht}\, u \neq \emptyset$ and $\mathrm{rht}\, u \vdash_{\mathbf{B}} Y'$; and

(iv''') $u \vdash_{\mathbf{A}+\mathbf{B}} (\Delta, \Delta)$ always holds,

where, in (iii), $u$ is any finite subset of $D_{\mathbf{A}+\mathbf{B}}$, in (iv')–(iv'''), $u \in \mathrm{Con}_{\mathbf{A}+\mathbf{B}}$, and we let:

$$\mathrm{lft}\, u = \{X \in D_{\mathbf{A}} \mid (X, \Delta) \in u\}, \quad \mathrm{rht}\, u = \{Y \in D_{\mathbf{B}} \mid (\Delta, Y) \in u\}.$$

$\blacksquare$

The plan of the sum definition is very similar to that for product, except that (1) for reasons to be made clear in examples, the parts do not share the least informative element (i.e. the data objects $(\Delta_{\mathbf{A}}, \Delta)$, $(\Delta, \Delta_{\mathbf{B}})$, and $(\Delta, \Delta)$ are inequivalent in this system), and (2) instead of defining consistency and entailment in a conjunctive way, these notions are defined disjunctively. The effect of these changes over Definition 6.1 is to produce a system $\mathbf{A} + \mathbf{B}$ whose elements divide into disjoint copies of those of $\mathbf{A}$ and $\mathbf{B}$ (plus an extra element $\perp_{\mathbf{A}+\mathbf{B}}$). These remarks can be made more precise in the following way:

**PROPOSITION 6.4.** If $\mathbf{A}$ and $\mathbf{B}$ are information systems, then so is $\mathbf{A} + \mathbf{B}$, and we have approximable mappings

$$\mathrm{inl} : \mathbf{A} \to \mathbf{A} + \mathbf{B} \quad \text{and} \quad \mathrm{inr} : \mathbf{B} \to \mathbf{A} + \mathbf{B},$$

such that, for approximable mappings

$$f : \mathbf{A} \to \mathbf{C} \quad \text{and} \quad g : \mathbf{B} \to \mathbf{C},$$

there is one and only one approximable mapping $[f, g] : \mathbf{A} + \mathbf{B} \to \mathbf{C}$, such that

$$[f, g] \circ \mathrm{inl} = f, \quad [f, g] \circ \mathrm{inr} = g, \quad \text{and} \quad [f, g](\perp_{\mathbf{A}+\mathbf{B}}) = \perp_{\mathbf{C}}.$$
*Proof.* The proof that 6.3 defines a system satisfying the basic axioms of 2.1 has to be left to the reader. Next using the notation of 6.1, where $\mathrm{lft}$ and $\mathrm{rht}$ were applied as operations on consistent sets $u \in \mathrm{Con}_{\mathbf{A}+\mathbf{B}}$, we redefine matters to have approximable mappings, where, for $v \in \mathrm{Con}_{\mathbf{A}}$ and $w \in \mathrm{Con}_{\mathbf{B}}$,

$(1)$ $v\ \mathrm{inl}\ u$ iff $\{(X, \Delta) \mid X \in v\} \vdash_{\mathbf{A}+\mathbf{B}} u$;

$(2)$ $w\ \mathrm{inr}\ u$ iff $\{(\Delta, Y) \mid Y \in w\} \vdash_{\mathbf{A}+\mathbf{B}} u$; and

$(3)$ $u\ [f, g]\ s$ iff either $\vdash_{\mathbf{C}}\ s$, or $\mathrm{lft}\, u \neq \emptyset$ and $\mathrm{lft}\, u\ f\ s$, or $\mathrm{rht}\, u \neq \emptyset$ and $\mathrm{rht}\, u\ g\ s$.

Because we defined $\mathbf{A} + \mathbf{B}$ so that consistency and entailment worked on the two halves of the set of data objects just as they worked on $\mathbf{A}$ and $\mathbf{B}$, respectively, it is easy to check that (1)–(3) define approximable mappings, and that the desired properties hold.

The uniqueness of $[f, g]$ comes from the fact that the elements of $\mathbf{A} + \mathbf{B}$, apart from the bottom element of the domain, are just the elements in the ranges of $\mathrm{inl}$ and $\mathrm{inr}$. Since the function $[f, g]$ takes bottom to bottom (in the indicated domains), it will be uniquely determined by what it does on the two halves of the sum. The last equations of the theorem just say that the function is completely determined on these elements. $\blacksquare$

It can also be shown that Propositions 6.2 and 6.4 uniquely characterize the domains $\mathbf{A} \times \mathbf{B}$ and $\mathbf{A} + \mathbf{B}$ up to isomorphism, and they give us the existence of additional mappings that are needed to show that product and sum are functors on the category of domains. We can also show from these results that the domain

$$\mathbf{BOOL} = \mathbf{1} + \mathbf{1}$$

has two elements $\mathrm{true}$ and $\mathrm{false}$, such that any mapping on $\mathbf{BOOL}$ is uniquely determined by its action on $\mathrm{true}$, $\mathrm{false}$ and $\perp_{\mathbf{BOOL}}$, and the values on the first two elements may be arbitrarily chosen.

**Lean 4**

- [InformationSystems/ProductsAndSumsOfDomains/Factoid65.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Factoid65/Basic.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/Basic.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_from_unit_eq_const.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_from_unit_eq_const.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_to_unit_eq_const.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/approxMap_to_unit_eq_const.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Factoid65/toElement_constMap_bot.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/toElement_constMap_bot.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitElement_eq_bot.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitElement_eq_bot.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitSystem.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Factoid65/unitSystem.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/Basic.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/Basic.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/BasicInst5.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/BasicInst5.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/BasicInst7.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/BasicInst7.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/IsProdToken.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/IsProdToken.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/ProdCon.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/ProdCon.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/ProdEnt.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/ProdEnt.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/ProdToken.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/ProdToken.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_funion.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_funion.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_insert_left.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_insert_left.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_insert_not_left.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_insert_not_left.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_mono.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_mono.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_singleton_left.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/fstFinset_singleton_left.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/instLeftCommutativeFstInsert.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/instLeftCommutativeFstInsert.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/instLeftCommutativeSndInsert.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/instLeftCommutativeSndInsert.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/mem_foldr_fst.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/mem_foldr_fst.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/mem_foldr_snd.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/mem_foldr_snd.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/mem_fstFinset.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/mem_fstFinset.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/mem_sndFinset.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/mem_sndFinset.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/prodBot.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/prodBot.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/productSystem.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/productSystem.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_funion.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_funion.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_insert_not_right.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_insert_not_right.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_insert_right.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_insert_right.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_mono.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_mono.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_singleton_right.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Product/sndFinset_singleton_right.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/Basic.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/Basic.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_liftLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_liftLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_liftRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/ProdCon_liftRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/comp_fstMap_pairMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/comp_fstMap_pairMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/comp_sndMap_pairMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/comp_sndMap_pairMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/element_eq_of_fst_snd.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/element_eq_of_fst_snd.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/entSet_fst_of_prodEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/entSet_fst_of_prodEntSet.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/entSet_snd_of_prodEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/entSet_snd_of_prodEntSet.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstFinset_liftLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstFinset_liftLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstFinset_liftRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstFinset_liftRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/fstMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/instLeftCommutativeMkLeftInsert.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/instLeftCommutativeMkLeftInsert.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/instLeftCommutativeMkRightInsert.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/instLeftCommutativeMkRightInsert.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/liftLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/liftLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/liftRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/liftRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/mem_liftLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/mem_liftLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/mem_liftRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/mem_liftRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/mkLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/mkLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/mkRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/mkRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/pairMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/pairMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/pairMap_unique.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/pairMap_unique.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndFinset_liftLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndFinset_liftLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndFinset_liftRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndFinset_liftRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition62/sndMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/Basic.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/Basic.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inlMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inlMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inrMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inrMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_botElement.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_botElement.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_unique.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_unique.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/copair_union_disj.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copair_union_disj.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_empty_of_rel_bot_like.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_empty_of_rel_bot_like.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_lft_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_lft_of_sumEntSet.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftLft_of_left_only.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftLft_of_left_only.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftRht_of_right_only.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftRht_of_right_only.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_rht_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_rht_of_sumEntSet.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inl_witness.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inl_witness.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inr_witness.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inr_witness.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/eq_botElement_of_no_injections.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/eq_botElement_of_no_injections.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap_toElement_sumElementLft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap_toElement_sumElementLft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap_toElement_sumElementRht.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap_toElement_sumElementRht.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_eq_empty_or_mem.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_eq_empty_or_mem.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_eq_empty_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_eq_empty_of_sumEntSet.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_mem_Con_of_SumCon_rht_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_mem_Con_of_SumCon_rht_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/not_mem_right_of_mem_left.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/not_mem_right_of_mem_left.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_eq_empty_or_mem.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_eq_empty_or_mem.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_eq_empty_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_eq_empty_of_sumEntSet.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_mem_Con_of_SumCon_lft_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_mem_Con_of_SumCon_lft_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/subset_botElement_of_projections_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/subset_botElement_of_projections_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementLft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementLft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementRht.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementRht.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumLftCarrier.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumLftCarrier.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumRhtCarrier.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumRhtCarrier.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/Basic.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/Basic.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_lft_con_of_lft_nonempty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_lft_con_of_lft_nonempty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_lft_empty_of_rht_nonempty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_lft_empty_of_rht_nonempty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_rht_con_of_rht_nonempty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_rht_con_of_rht_nonempty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_rht_empty_of_lft_nonempty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/SumCon_rht_empty_of_lft_nonempty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/SumEnt.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/SumEnt.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/SumToken.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/SumToken.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/instDecidableEqSumToken.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/instDecidableEqSumToken.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/instLeftCommutativeLftInsert.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/instLeftCommutativeLftInsert.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/instLeftCommutativeRhtInsert.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/instLeftCommutativeRhtInsert.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_funion.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_funion.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_insert_bot.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_insert_bot.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_insert_left.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_insert_left.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_insert_right.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_insert_right.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_mono.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_mono.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_singleton_bot.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_singleton_bot.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_singleton_left.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/lftFinset_singleton_left.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/lftInsert.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/lftInsert.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/mem_foldr_lft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/mem_foldr_lft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/mem_foldr_rht.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/mem_foldr_rht.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/mem_lftFinset.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/mem_lftFinset.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/mem_rhtFinset.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/mem_rhtFinset.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_funion.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_funion.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_insert_bot.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_insert_bot.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_insert_left.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_insert_left.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_insert_right.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_insert_right.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_mono.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_mono.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_singleton_bot.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_singleton_bot.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_singleton_right.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/rhtFinset_singleton_right.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/rhtInsert.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/rhtInsert.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/sumBot.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/sumBot.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Sum/sumSystem.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Sum/sumSystem.lean)
