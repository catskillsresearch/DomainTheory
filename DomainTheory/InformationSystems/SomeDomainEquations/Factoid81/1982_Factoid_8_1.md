# Factoid 8.1

*A domain of trees or S-expressions.* This is everyone’s favorite example. And a very nice example it is, but we should not think that it contains all the meat of the theory of domain equations. Even if we generalize the kinds of equations to contain all iterations of the domain constructs $+$ and $\times$, the full power of the method has not been exploited. We will try to make this clear in the further examples.

Let a domain (information system) $\mathbf{A}$ be given. What we want to construct is a domain $\mathbf{T}$ of “trees” built up from elements of $\mathbf{A}$ as “atoms”. For simplicity we consider unlabelled binary trees here, but more complex trees are easy to accommodate. The domain equation we want to “solve” is this one:

$$\mathbf{T} \cong \mathbf{A} + (\mathbf{T} \times \mathbf{T}).$$
If such a domain exists, then we can say that (up to isomorphism) the elements of the domain $\mathbf{T}$ are either bottom, or elements of the given domain $\mathbf{A}$, or pairs of elements from the domain $\mathbf{T}$ itself. And these are the only kinds of elements that $\mathbf{T}$ has.

To prove that such a domain exists it is only necessary to ask what information has to be given about a prospective element. The answer may involve us in a regress, but the running backwards need not be infinite—at least for the finite elements. As we shall see, the infinite elements of $\mathbf{T}$ can be self-replicating; but, to define a domain fully, all we have to do is to build up the finite elements out of the data objects in a systematic way. Fortunately, in order to satisfy the above equation, the required closure conditions on data objects are simple to achieve.

In the first place, we need copies of all the data objects of $\mathbf{A}$ to put into the sum. The easy way to do this is to take an object $\Delta$ not in $D_{\mathbf{A}}$, and to let, by definition,

$$\Delta_{\mathbf{T}} = (\Delta, \Delta).$$

That gives us one member of $D_{\mathbf{T}}$, the one we always have to have in any case. The copy of an $X \in D_{\mathbf{A}}$ is just going to be $(X, \Delta)$. The other members of $D_{\mathbf{T}}$ will be of the form $(\Delta, U)$, where $U$ gives us information about the other kind of elements of $\mathbf{T}$. The point is that $\mathbf{T}$ has to be a sum, and we are using just the scheme of Definition 6.3 to set this up.

Next we have to think what kind of information the $U$ above should contain. Because we want a product, we refer back to Definition 6.1 and imagine we have already defined $D_{\mathbf{T}}$. What 6.1(i) suggests is that we throw in a bunch of other data objects into $D_{\mathbf{T}}$. The only point that needs care is that the data objects for the product must be copied into the overall sum. With this in mind, the following clauses give us the inductive definition of $D_{\mathbf{T}}$:

(1) $\Delta_{\mathbf{T}} \in D_{\mathbf{T}}$;

(2) $(X, \Delta) \in D_{\mathbf{T}}$ whenever $X \in D_{\mathbf{A}}$; and

(3) $(\Delta, (Y, \Delta_{\mathbf{T}})) \in D_{\mathbf{T}}$, and $(\Delta, (\Delta_{\mathbf{T}}, Z)) \in D_{\mathbf{T}}$ whenever $Y, Z \in D_{\mathbf{T}}$.

Of course, when we say “inductive definition,” we mean that $D_{\mathbf{T}}$ is the least class satisfying (1)–(3). By standard arguments it can be shown that $D_{\mathbf{T}}$ satisfies this set-theoretical equation:

$$D_{\mathbf{T}} = \{\Delta_{\mathbf{T}}\} \cup \{(X, \Delta) \mid X \in D_{\mathbf{A}}\} \cup \{(\Delta, (Y, \Delta_{\mathbf{T}})) \mid Y \in D_{\mathbf{T}}\} \cup \{(\Delta, (\Delta_{\mathbf{T}}, Z)) \mid Z \in D_{\mathbf{T}}\}.$$

In fact, with some very mild assumptions about ordered pairs in set theory, $D_{\mathbf{T}}$ is the only solution to the above equation.

Defining the data objects is but part of the story: the same data objects can enter into quite different information systems. Data objects are just “tokens” and are only given “meaning” when $\mathrm{Con}_{\mathbf{T}}$ and $\vdash_{\mathbf{T}}$ are defined. Let us consider the problem of consistency first. We already understand the notion as it applies to sum and product systems, so we must merely copy over the parts of the previous definitions in the right position for the definition of $\mathrm{Con}_{\mathbf{T}}$. There are two forms we could give this definition; perhaps the best is the inductive one. We have:

(4) $\emptyset \in \mathrm{Con}_{\mathbf{T}}$;

(5) $u \cup \{\Delta_{\mathbf{T}}\} \in \mathrm{Con}_{\mathbf{T}}$ whenever $u \in \mathrm{Con}_{\mathbf{T}}$;
(6) $\{(X, \Delta) \mid X \in w\} \in \mathrm{Con}_{\mathbf{T}}$ whenever $w \in \mathrm{Con}_{\mathbf{A}}$;

(7) $\{(\Delta, (Y, \Delta_{\mathbf{T}})) \mid Y \in u\} \cup \{(\Delta, (\Delta_{\mathbf{T}}, Z)) \mid Z \in v\} \in \mathrm{Con}_{\mathbf{T}}$ whenever $u, v \in \mathrm{Con}_{\mathbf{T}}$.

Conditions (4)–(7) certainly make the inductive character of $\mathrm{Con}_{\mathbf{T}}$ clear—again, let us emphasize, the set being specified is the least such. Also clear from the definition is the fact that a consistent set of $\mathbf{T}$—aside from containing $\Delta_{\mathbf{T}}$—is either a copy of a consistent set of $\mathbf{A}$ or a copy of a consistent set of $\mathbf{T} \times \mathbf{T}$. We could thus state a set-theoretical equation for $\mathrm{Con}_{\mathbf{T}}$ similar to the one for $D_{\mathbf{T}}$.

It remains to define entailment for $\mathbf{T}$. Here are the inductive clauses which are pretty much forced on us by our objective of solving the domain equation:

(8) $u \vdash_{\mathbf{T}} \Delta_{\mathbf{T}}$ always;

(9) $u \cup \{\Delta_{\mathbf{T}}\} \vdash_{\mathbf{T}} Y$ whenever $u \vdash_{\mathbf{T}} Y$;

(10) $\{(X, \Delta) \mid X \in w\} \vdash_{\mathbf{T}} (W, \Delta)$ whenever $w \vdash_{\mathbf{A}} W$;

(11) $\{(\Delta, (Y, \Delta_{\mathbf{T}})) \mid Y \in u\} \cup \{(\Delta, (\Delta_{\mathbf{T}}, Z)) \mid Z \in v\} \vdash_{\mathbf{T}} (\Delta, (X, \Delta_{\mathbf{T}}))$ whenever $u \vdash_{\mathbf{T}} X$ and $v \in \mathrm{Con}_{\mathbf{T}}$; and

(12) $\{(\Delta, (Y, \Delta_{\mathbf{T}})) \mid Y \in u\} \cup \{(\Delta, (\Delta_{\mathbf{T}}, Z)) \mid Z \in v\} \vdash_{\mathbf{T}} (\Delta, (\Delta_{\mathbf{T}}, X))$ whenever $v \vdash_{\mathbf{T}} X$ and $u \in \mathrm{Con}_{\mathbf{T}}$.

Inductive definitions engender inductive proofs. It now has to be checked that consistency and entailment for $\mathbf{T}$ satisfy the axioms of 2.1. The steps needed for this check are mechanical. (The proof may be aided by noting that the cases in (4)–(7) and in (8)–(12) are disjoint—except for a trivial overlap between (8) and (9). The cases get invoked typically by asking, when confronted with an entailment to prove, for the nature of the data object on the right of the turnstile.)

Having defined and verified that $\mathbf{T}$ is an information system, the validity of the domain equation for $\mathbf{T}$ is secured by forming the right-hand side and noting that $\mathbf{T}$ is *identical* to $\mathbf{A} + (\mathbf{T} \times \mathbf{T})$. The reason is that we carefully chose the notation to match the official definitions of sums and products. (In general, in solving domain equations some transformation might have to take place to “re-format” data objects if things are not set up to be literally the same.)

It should be remarked that the sense can be made precise in which $\mathbf{T}$ is the *least* solution of the given domain equation. (It is an initial algebra in a suitable category of algebras and algebra homomorphisms.) It is pretty obvious that it is minimal in some sense, because we put into it only what was strictly required by the problem and nothing more.

It is also fairly obvious that there are *many* solutions to this domain equation. A non-constructive way to obtain non-minimal solutions is to interpret the whole construction of $\mathbf{T}$ in a non-standard model of set theory. Though, in the definition of $D_{\mathbf{T}}$, it looks like we are only working with very finite objects, everything we did could be made abstract and could be carried out in some funny universe. The result would be a system of “finite” data objects having all the right formal properties but containing things not in the standard minimal system. We would then take the notions of consistency and entailment that also exist in the funny universe and
restrict them to sets of data objects that are actually finite in the standard sense. It can be seen from the formal properties of the construction that the resulting notions satisfy our axioms for an information system and that the domain equation holds—BUT the system would have many different elements beyond what we put into the original $\mathbf{T}$. To make this construction work, by the way, we would have to force $\mathbf{A}$ to be absolute in the model: if it is actually finite (say, $\mathbf{A} = \mathbf{BOOL}$), then there is no problem. (Constructive methods for introducing “nonstandard” data objects can also be given.)

Finally, we must remark on why we called $\mathbf{T}$ a domain of $S$-expressions. The answer becomes clear when we structure $\mathbf{T}$ as an algebra. First, there is an approximable mapping

$$\mathrm{atom} : \mathbf{A} \to \mathbf{T},$$

which injects $\mathbf{A}$ into $\mathbf{T}$ making the elements of $\mathbf{A}$ “atoms” of $\mathbf{T}$. Then there is a truth-valued predicate on $\mathbf{T}$ which decides whether an element is an atom:

$$\mathrm{isatom} : \mathbf{T} \to \mathbf{BOOL}.$$

Finally, since $\mathbf{T} \times \mathbf{T}$ is a part of $\mathbf{T}$, we can redefine the paring functions so that:

$$\mathrm{pair} : \mathbf{T} \times \mathbf{T} \to \mathbf{T}, \quad \mathrm{fst} : \mathbf{T} \to \mathbf{T}, \quad \text{and } \mathrm{snd} : \mathbf{T} \to \mathbf{T}.$$

In LISP terminology, these operations are the same as the familiar cons, car, and cdr. This makes $\mathbf{T}$ into an algebra where, starting from atoms, elements—expressions—can be built up by iterated pairing.

But why is our system different from the usual way of regarding $S$-expressions? The answer is that by including partial expressions (those involving $\Delta_{\mathbf{T}}$) and by completing the domain with limits, *infinite* expressions are introduced. For instance, if $a \in |\mathbf{T}|$, then we can solve the fixed-point equation:

$$x = \mathrm{pair}(\mathrm{atom}(a), x),$$

which is an infinite list of $a$’s. This is but one example; the possibilities have been discussed in many papers too numerous to mention here.

As is common to remark, $S$-expressions can also be thought of as trees: the parse tree that gives the grammatical form of the expression. What we have added to the idea of a tree is the possibility of having infinite trees, and having all these trees as elements of a domain. $\blacksquare$

**Lean 4**

- [InformationSystems/SomeDomainEquations/Factoid81.lean](../Factoid81.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/Basic.lean](Basic.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon.lean](TreeCon.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_atom_con_of_atoms.lean](TreeCon_atom_con_of_atoms.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_atoms_empty_of_right.lean](TreeCon_atoms_empty_of_right.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_empty.lean](TreeCon_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_insert_bot.lean](TreeCon_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_insert_of_ent.lean](TreeCon_insert_of_ent.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_pairL_of_right.lean](TreeCon_pairL_of_right.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_pairR_of_right.lean](TreeCon_pairR_of_right.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_pairs_empty_of_left.lean](TreeCon_pairs_empty_of_left.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_singleton.lean](TreeCon_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_subset.lean](TreeCon_subset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEnt.lean](TreeEnt.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload.lean](TreeEntPayload.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload_of_mem.lean](TreeEntPayload_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload_of_no_atoms_no_pairs.lean](TreeEntPayload_of_no_atoms_no_pairs.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload_trans.lean](TreeEntPayload_trans.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEnt_of_mem.lean](TreeEnt_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEnt_trans.lean](TreeEnt_trans.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeToken.lean](TreeToken.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset.lean](atomFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_empty.lean](atomFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_atom.lean](atomFinset_insert_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_bot.lean](atomFinset_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_pairL.lean](atomFinset_insert_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_pairR.lean](atomFinset_insert_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_mono.lean](atomFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_atom.lean](atomFinset_singleton_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_bot.lean](atomFinset_singleton_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_pairL.lean](atomFinset_singleton_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_pairR.lean](atomFinset_singleton_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomInsert.lean](atomInsert.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/eq_singleton_bot_of_subset.lean](eq_singleton_bot_of_subset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/mem_atomFinset.lean](mem_atomFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/mem_foldr_atom.lean](mem_foldr_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/mem_pairLFinset.lean](mem_pairLFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/mem_pairRFinset.lean](mem_pairRFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset.lean](pairLFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_empty.lean](pairLFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_atom.lean](pairLFinset_insert_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_bot.lean](pairLFinset_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_pairL.lean](pairLFinset_insert_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_pairR.lean](pairLFinset_insert_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_mono.lean](pairLFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_atom.lean](pairLFinset_singleton_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_bot.lean](pairLFinset_singleton_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_pairL.lean](pairLFinset_singleton_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_pairR.lean](pairLFinset_singleton_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairL_ne_or_subset_bot.lean](pairL_ne_or_subset_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset.lean](pairRFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_empty.lean](pairRFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_atom.lean](pairRFinset_insert_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_bot.lean](pairRFinset_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_pairL.lean](pairRFinset_insert_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_pairR.lean](pairRFinset_insert_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_mono.lean](pairRFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_atom.lean](pairRFinset_singleton_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_bot.lean](pairRFinset_singleton_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_pairL.lean](pairRFinset_singleton_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_pairR.lean](pairRFinset_singleton_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairR_ne_or_subset_bot.lean](pairR_ne_or_subset_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeBot.lean](treeBot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeRhs.lean](treeRhs.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeRhs_eq_sum_product.lean](treeRhs_eq_sum_product.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeSystem.lean](treeSystem.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold.lean](treeUnfold.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_atom.lean](treeUnfold_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_bot.lean](treeUnfold_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_pairL.lean](treeUnfold_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_pairL_bot_eq_pairR_bot.lean](treeUnfold_pairL_bot_eq_pairR_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_pairR.lean](treeUnfold_pairR.lean)
