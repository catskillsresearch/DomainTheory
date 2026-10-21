# Example 6.2

**EXAMPLE 6.2.** Our staple examples $B$ and $C$ satisfy “domain equations” in the form of isomorphisms as we have previously seen. Indeed

$$
B \cong B + B, \text{ and}
$$

$$
C \cong \{\{\Lambda\}\} + C + C,
$$

where if we liked we could construct both systems over $\{0,1\}^*$ and have:

$$
B = \{\{0,1\}^*\} \cup \{0X \mid X \in B\} \cup \{1X \mid X \in B\}, \text{ and}
$$

$$
C = \{\{0,1\}^*\} \cup \{\{\Lambda\}\} \cup \{0X \mid X \in C\} \cup \{1X \mid X \in C\}.
$$

We leave to the exercises the explanations of what kinds of algebras $B$ and $C$ are and why they are initial. Here we want to propose a simple, yet interesting generalization of $B$.

Consider this domain equation:

$$
A \cong A^n + A^n,
$$

where $A^n$ stands for the $n$-fold cartesian power of $A$. We can, with the aid of some encoding solve this equation as a neighbourhood system over $\{0,1\}^*$ as follows:

$$
A = \{\{0,1\}^*\} \cup \bigcup_{i=0,1} \left\{ i \bigcup_{j < n} 1^j 0 X_j \mid X_j \in A \text{ for all } j < n \right\}.
$$

For instance, if $n = 3$, then a typical neighbourhood in $A$ is something like

$$
00X_0 \cup 010X_1 \cup 0110X_2,
$$

where $X_0, X_1, X_2 \in A$. The first ‘0’ could also be a ‘1’ in front of each of the terms.

In words, an element of $A$ (other than $\bot$) is an $n$-tuple of elements of $A$: but there are two separate copies of these, the left one and the right one. We can write for $a \in |A|$

$$
a = \pm \langle a_0, a_1, \ldots, a_{n-1} \rangle,
$$

where $+$ is chosen if $a$ is on the right, and $-$ if on the left. As a tree diagram $a$ might look like this for $n = 3$:
```
                         a  +
                        / | \
                       + a₁− +
                      /|\ /|\ /|\
                     + − − + + a₁₂− − + −
                    etc. etc. etc.
```

That is, $a$ is an infinite ternary tree with $+$ or $-$ labels at each node. If each node (subtree) is truly infinite, the element is *total*; if $\perp$ is ever encountered, it is only *partial*; if every branch ends with $\perp$, the tree is a *finite element* of $|A|$.

What can be done with such trees? Let $\sigma \in \{0, 1, \ldots, n-1\}^*$ be a finite sequence of "digits" each less than $n$. We let $\Sigma = \{0, 1, \ldots, n-1\}$. We can define for $a \in |A|$ the operation $\sigma \mapsto a\sigma$ by recursion on $\sigma$:

$$
a \Lambda = a, \text{ and}
$$

$$
a i \sigma = (a_i) \sigma.
$$

The $a\sigma$ are just the *subtrees* of $a$ with $\sigma$ as a *selector*. We also have a map

$$
\mathrm{pos} : A \to T
$$

where

$$
\mathrm{pos}(+\langle a_0, a_1, \ldots, a_{n-1} \rangle) = \mathrm{true}, \text{ and}
$$

$$
\mathrm{pos}(-\langle a_0, a_1, \ldots, a_{n-1} \rangle) = \mathrm{false}.
$$

We say that a (total) tree $a$ is *eventually periodic* iff the set $\{a\sigma \mid \sigma \in \Sigma^*\}$ is finite. The result is that the "language"

$$
L_a = \{\sigma \in \Sigma^* \mid \mathrm{pos}(a\sigma) = \mathrm{true}\}
$$

corresponding to an eventually periodic tree is always a *regular event* of automata theory, and every such language has this form. In fact, $a$ just represents the initial state of an automaton, and $a\sigma$ represents the state after "reading" a tape $\sigma$. $\square$
In order to formulate more generally the idea of a domain equation and initial algebra, we must introduce a small amount of the terminology of category theory. To be as specific as possible, think of systems $D$ over sets $\Delta \subseteq \Sigma^*$ with $\Sigma = \{0, 1\}$, say. They form quite an interesting category with respect to the approximable maps $f : D \to D'$. Recall that to be a category of "domains" and "maps" all that is required is an associative composition $g \circ f$ of maps with identity maps $I : D \to D$ for each domain of the category. And this we certainly have for the systems indicated. And there are many other categories waiting around: for instance, restrict systems to those where $\emptyset \notin D$. This is not much of a restriction, as every system is isomorphic to one like this. Or restrict the maps to being the strict maps $f : D \to D'$ where $f(\bot_D) = \bot_{D'}$. This is an essentially different, though related category. We shall find many others.

What examples 6.1 and 6.2 suggest is the notion of a construct which makes new domains out of old. For example, with $D$ fixed, 6.1 suggests for any domain $X$ over $\Gamma \subseteq \Sigma^*$ a domain

$$
T(X) = D + (X \times X).
$$

More specifically (converting from $\Sigma = \{0, 1, 2\}$ to $\Sigma = \{0, 1\}$) we could write

$$
T(X) = \{\Gamma'\} \cup \{0X \mid X \in D\} \cup \{10X \cup 11Y \mid X, Y \in X\},
$$

where we have $\Gamma' = 0\Delta \cup 10\Gamma \cup 11\Gamma$. (By the way, here we definitely want to assume $\emptyset \notin D$ and $\emptyset \notin X$ and to get $\emptyset \notin T(X)$.) This construct is an example of a *functor*, a notion that can be defined abstractly on any category.

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/Example62.lean](Example62.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/BB.lean](Example62/BB.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/B_domain_equation.lean](Example62/B_domain_equation.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/B_nonempty.lean](Example62/B_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/Basic.lean](Example62/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/bbEquiv.lean](Example62/bbEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit.lean](Example62/embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_cone.lean](Example62/embBit_cone.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_eq_prepend.lean](Example62/embBit_eq_prepend.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_injective.lean](Example62/embBit_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_inter.lean](Example62/embBit_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_inter_ne.lean](Example62/embBit_inter_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_ne.lean](Example62/embBit_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_ne_univ.lean](Example62/embBit_ne_univ.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_nonempty.lean](Example62/embBit_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_subset.lean](Example62/embBit_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/fromBB.lean](Example62/fromBB.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/fromBB_mem_embF.lean](Example62/fromBB_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/fromBB_mem_embT.lean](Example62/fromBB_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/fromBB_toBB.lean](Example62/fromBB_toBB.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/memB_cases.lean](Example62/memB_cases.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/memB_embBit.lean](Example62/memB_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/memB_embBit_inv.lean](Example62/memB_embBit_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/mem_embBit.lean](Example62/mem_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/nil_not_mem_embBit.lean](Example62/nil_not_mem_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/sum_mem_inj₀_inv.lean](Example62/sum_mem_inj₀_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/sum_mem_inj₁_inv.lean](Example62/sum_mem_inj₁_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/sum_mem_nonempty.lean](Example62/sum_mem_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/toBB.lean](Example62/toBB.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/toBB_fromBB.lean](Example62/toBB_fromBB.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/toBB_mem_inj₀.lean](Example62/toBB_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/toBB_mem_inj₁.lean](Example62/toBB_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A.lean](Example62A.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/AAsys.lean](Example62A/AAsys.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/A_domain_equation.lean](Example62A/A_domain_equation.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/Apow.lean](Example62A/Apow.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/Asys.lean](Example62A/Asys.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/Asys_master.lean](Example62A/Asys_master.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/Asys_mem.lean](Example62A/Asys_mem.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/Basic.lean](Example62A/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/MemA.lean](Example62A/MemA.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aaEquiv.lean](Example62A/aaEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₀.lean](Example62A/aa_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₀_inv.lean](Example62A/aa_mem_inj₀_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₁.lean](Example62A/aa_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₁_inv.lean](Example62A/aa_mem_inj₁_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_nonempty.lean](Example62A/aa_mem_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/apowNe.lean](Example62A/apowNe.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/apow_mem_prodN.lean](Example62A/apow_mem_prodN.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/apow_mem_prodN_inv.lean](Example62A/apow_mem_prodN_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple.lean](Example62A/embTuple.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_injective.lean](Example62A/embTuple_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_inter.lean](Example62A/embTuple_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_inter_ne.lean](Example62A/embTuple_inter_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_ne.lean](Example62A/embTuple_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_ne_univ.lean](Example62A/embTuple_ne_univ.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_nonempty.lean](Example62A/embTuple_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_subset.lean](Example62A/embTuple_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/fromAA.lean](Example62A/fromAA.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/fromAA_mem_embF.lean](Example62A/fromAA_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/fromAA_mem_embT.lean](Example62A/fromAA_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/fromAA_toAA.lean](Example62A/fromAA_toAA.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/memA_inter.lean](Example62A/memA_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/memA_nonempty.lean](Example62A/memA_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/memA_tuple_inv.lean](Example62A/memA_tuple_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/mem_embTuple.lean](Example62A/mem_embTuple.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/mem_prodN.lean](Example62A/mem_prodN.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/nil_not_mem_embTuple.lean](Example62A/nil_not_mem_embTuple.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/npow.lean](Example62A/npow.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/npow_mem.lean](Example62A/npow_mem.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/npow_nonempty.lean](Example62A/npow_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/prodN.lean](Example62A/prodN.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/prodN_injective.lean](Example62A/prodN_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/prodN_inter.lean](Example62A/prodN_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/prodN_subset.lean](Example62A/prodN_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/slotPre.lean](Example62A/slotPre.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/slotPre_inj.lean](Example62A/slotPre_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/slot_list_inj.lean](Example62A/slot_list_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/tag_eq_of_subset.lean](Example62A/tag_eq_of_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/toAA.lean](Example62A/toAA.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/toAA_fromAA.lean](Example62A/toAA_fromAA.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/toAA_mem_inj₀.lean](Example62A/toAA_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/toAA_mem_inj₁.lean](Example62A/toAA_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C.lean](Example62C.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/Basic.lean](Example62C/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/CC.lean](Example62C/CC.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/C_domain_equation.lean](Example62C/C_domain_equation.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/C_nonempty.lean](Example62C/C_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/ccEquiv.lean](Example62C/ccEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/embBit_singleton.lean](Example62C/embBit_singleton.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/eq_master3_of_subset.lean](Example62C/eq_master3_of_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/fromCC.lean](Example62C/fromCC.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/fromCC_mem_embF.lean](Example62C/fromCC_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/fromCC_mem_embT.lean](Example62C/fromCC_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/fromCC_mem_nil.lean](Example62C/fromCC_mem_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/fromCC_toCC.lean](Example62C/fromCC_toCC.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0.lean](Example62C/j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_injective.lean](Example62C/j0_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_inter_j0.lean](Example62C/j0_inter_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_inter_j1.lean](Example62C/j0_inter_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_inter_j2.lean](Example62C/j0_inter_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_nonempty.lean](Example62C/j0_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_subset_j0.lean](Example62C/j0_subset_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_subset_master3.lean](Example62C/j0_subset_master3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1.lean](Example62C/j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_injective.lean](Example62C/j1_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_inter_j1.lean](Example62C/j1_inter_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_inter_j2.lean](Example62C/j1_inter_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_nonempty.lean](Example62C/j1_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_subset_j1.lean](Example62C/j1_subset_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_subset_master3.lean](Example62C/j1_subset_master3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2.lean](Example62C/j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2_injective.lean](Example62C/j2_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2_inter_j2.lean](Example62C/j2_inter_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2_nonempty.lean](Example62C/j2_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2_subset_j2.lean](Example62C/j2_subset_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2_subset_master3.lean](Example62C/j2_subset_master3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/master3.lean](Example62C/master3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/master3_inter_j0.lean](Example62C/master3_inter_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/master3_inter_j1.lean](Example62C/master3_inter_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/master3_inter_j2.lean](Example62C/master3_inter_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/memC_cases.lean](Example62C/memC_cases.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/memC_embBit.lean](Example62C/memC_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/memC_embBit_inv.lean](Example62C/memC_embBit_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/none_mem_master3.lean](Example62C/none_mem_master3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/none_not_mem_j0.lean](Example62C/none_not_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/none_not_mem_j1.lean](Example62C/none_not_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/none_not_mem_j2.lean](Example62C/none_not_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/singleton_nil_inter_embBit.lean](Example62C/singleton_nil_inter_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/singleton_nil_ne_embBit.lean](Example62C/singleton_nil_ne_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/singleton_nil_ne_univ.lean](Example62C/singleton_nil_ne_univ.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/sum3.lean](Example62C/sum3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/sum3_mem_j1_inv.lean](Example62C/sum3_mem_j1_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/sum3_mem_j2_inv.lean](Example62C/sum3_mem_j2_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/sum3_mem_nonempty.lean](Example62C/sum3_mem_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t0.lean](Example62C/t0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t0_mem_j0.lean](Example62C/t0_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t0_not_mem_j1.lean](Example62C/t0_not_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t0_not_mem_j2.lean](Example62C/t0_not_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t1.lean](Example62C/t1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t1_mem_j1.lean](Example62C/t1_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t1_not_mem_j0.lean](Example62C/t1_not_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t1_not_mem_j2.lean](Example62C/t1_not_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t2.lean](Example62C/t2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t2_mem_j2.lean](Example62C/t2_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t2_not_mem_j0.lean](Example62C/t2_not_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t2_not_mem_j1.lean](Example62C/t2_not_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/toCC.lean](Example62C/toCC.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/toCC_fromCC.lean](Example62C/toCC_fromCC.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/toCC_mem_j0.lean](Example62C/toCC_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/toCC_mem_j1.lean](Example62C/toCC_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/toCC_mem_j2.lean](Example62C/toCC_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/unitSys_nonempty.lean](Example62C/unitSys_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular.lean](Example62Regular.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/Basic.lean](Example62Regular/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/EventuallyPeriodic.lean](Example62Regular/EventuallyPeriodic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/Tree.lean](Example62Regular/Tree.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/child.lean](Example62Regular/child.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/eventuallyPeriodic_iff_isRegular.lean](Example62Regular/eventuallyPeriodic_iff_isRegular.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/isRegular_iff_exists_eventuallyPeriodic.lean](Example62Regular/isRegular_iff_exists_eventuallyPeriodic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/mem_treeLang.lean](Example62Regular/mem_treeLang.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/pos.lean](Example62Regular/pos.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/pos_select.lean](Example62Regular/pos_select.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/select.lean](Example62Regular/select.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/select_append.lean](Example62Regular/select_append.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/select_apply.lean](Example62Regular/select_apply.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/select_cons.lean](Example62Regular/select_cons.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/select_nil.lean](Example62Regular/select_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang.lean](Example62Regular/treeLang.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang_eq_pos.lean](Example62Regular/treeLang_eq_pos.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang_injective.lean](Example62Regular/treeLang_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang_select.lean](Example62Regular/treeLang_select.lean)
