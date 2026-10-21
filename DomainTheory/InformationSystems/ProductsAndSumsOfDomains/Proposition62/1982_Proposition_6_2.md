# Proposition 6.2

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

**Lean 4**

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
