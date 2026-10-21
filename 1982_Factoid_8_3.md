# Factoid 8.3

*A universal domain.* As a final example of building up domains recursively, we give a construction of a “universal” domain $U$. (The reason for the name will be explained presently.) The best way to define $U$ seems to be to define a domain $V$ with a top element first, and then to remove the top.

The recursion for $V$ is remarkably simple. We begin with two distinct objects $\Delta$ and $\nabla$ that give information about the bottom and top of $V$, respectively. Thus, $\Delta_V = \Delta$ by definition. We assume that these two special data objects are “atomic” in the sense that they are not equal to any ordered pair of objects. For the definition of $D_V$ we have these clauses:

(1) $\Delta, \nabla \in D_V$;

(2) $(X, \Delta) \in D_V$ and $(\Delta, Y) \in D_V$ whenever $X, Y \in D_V$.

In other words, we begin with two objects and close up under two flavors of copies of these objects. (A product result is involved here, so that is the reason for structuring the flavors the way we have.)

For $V$ all subsets of $D_V$ are consistent, so all we have left is to define entailment for this domain. The clauses are:

(3) $u \vdash_V \Delta$ always;

(4) $u \vdash_V \nabla$ whenever either $\nabla \in u$ or $\{X \mid (X, \Delta) \in u\} \vdash_V \nabla$ and $\{Y \mid (\Delta, Y) \in u\} \vdash_V \nabla$;

(5) $u \vdash_V (X', \Delta)$ whenever either $\nabla \in u$ or $\{X \mid (X, \Delta) \in u\} \vdash_V X'$; and

(6) $u \vdash_V (\Delta, Y')$ whenever either $\nabla \in u$ or $\{Y \mid (\Delta, Y) \in u\} \vdash_V Y'$.

The proof that $V$ is an information system proceeds as before. Note that, under the above definition of entailment, the data objects $\Delta$, $(\Delta, \Delta)$, $((\Delta, \Delta), \Delta)$, etc. are all equivalent. There is, however, no other data object equivalent to $\nabla$. The domain equation satisfied by $V$ is:

$$V \cong V \times V.$$

Of course, there are an unlimited number of solutions to this equation, so the fact that $V$ satisfies it tells us very little.

Because $\nabla$ entails everything, we can regard it as a “rogue” object that ought to be banned from polite company: the only element of $V$ it gives any information about is the top element, which is as unhelpful as any element could be. We should simply throw it out as being “inconsistent.” What remains is the domain $U$. Formally we have:

(7) $D_U = D_V - \{\nabla\}$;

(8) $\Delta_U = \Delta_V$;

(9) $\mathrm{Con}_U = \{u \subseteq D_U \mid u \text{ finite and } u \nvdash_V \nabla\}$; and

(10) $u \vdash_U Y$ iff $u \in \mathrm{Con}_U$, $Y \in D_U$ and $u \vdash_V Y$.
The same style of definition would work in any situation when an information system has a rogue data object that entails everything: there always is a system that results from eliminating all those objects that entail everything. Indeed, we could have always included such an object in any domain and altered the definition to take as elements those deductively closed sets of data objects that *do* not have the rogue object as a member. We did not do this for the reason that superfluous elements cause lots of exceptions in constructs such as product, where there is a temptation to let them enter into various combinations.

Now in $U$ we *do* allow $\nabla$ to enter into combinations—and this is part of the secret of the construction. The consequence is, however, that the domain equation which $U$ satisfies is not too easy to state since it involves an unfamiliar functor. So it is not through such equations that we will understand its nature in a direct way. But it is possible to explain how it works by reference to the steps in the construction.

Imagine the full (infinite) binary tree. The data objects of $U$ are giving information about possible paths in the tree. We think to the tree starting at the root node at the top of the page and growing down. The object $\Delta$ gives no information—so no paths are *excluded*. (If we would have allowed $\nabla$, then the information it would have been giving is that all paths are excluded.) The data object $(X, \Delta)$ tells us about a path that *either* it is unrestricted on the right half of the tree, *or* on the left, when we start at the node directly below the root, the paths that are excluded from the subtree are those excluded according to $X$. This makes sense because the subtrees of the binary tree look exactly like the whole tree, so information can be relativized or translated to other positions. With $(\Delta, Y)$ the rôles of right and left are interchanged. We could have introduced data objects of the form $(X, Y)$ which tell us information about both halves of the tree at the same time, but the consistent set $\{(X, \Delta), (\Delta, Y)\}$ does the same job. In general consistent sets should be thought of as *conjunctions*; while, in this example, the comma in the ordered pair should be thought of as a *disjunction* when “reading” information objects.

We can now see that a single data object (if it contains $\nabla$) looks down the tree along a finite path to some depth and then *excludes* the rest of the tree below that node. A consistent set of data objects leaves at least one hole, so at least one path is not excluded. The maximal consistent sets of information objects are those giving true information about one single (infinite) path—the total elements of the domain $U$ correspond exactly to the infinite paths in the binary tree. The partial elements are harder to describe geometrically, however. In accumulating information into a consistent set, holes can be left all over the tree. A partial object is therefore of an indeterminate character, since the “path” we are describing might sneak through any one of the holes. (There is, by the way, a precise topological explanation of what is happening. The total elements of $U$ form a well-known topological space, the so-called Cantor space, and the partially ordered set of elements of $U$ is isomorphic to the lattice of *open* sets of the space—save that the whole space is not allowed.)

This is all very well, but what, we ask, is the good of this domain, and why is it called “universal”. The proof cannot be given here, but the result is as follows. As a consequence of standard facts about countable Boolean algebras, it can be proved that every “countably based” domain is a subdomain of $U$. More specifically, if $\mathbf{A}$ is an information system, and if $D_{\mathbf{A}}$ is countable, then there exists a pair of approximable mappings

$$a : \mathbf{A} \to \mathbf{U} \text{ and } b : \mathbf{U} \to \mathbf{A},$$
such that

$$b \circ a = I_{\mathbf{A}} \text{ and } a \circ b \subseteq I_{\mathbf{U}}.$$

This makes $\mathbf{A}$ a special kind of retract of $\mathbf{U}$. The mappings $a$ and $b$ are far from unique, but at least there is one way to give a one-one embedding of the elements of $\mathbf{A}$ into the elements of $\mathbf{U}$.

The universal property of $\mathbf{U}$ can be applied quite widely. For example, since $(\mathbf{U} \to \mathbf{U})$ is a system with only countably many data objects (by explicit construction!), this system is a retract of $\mathbf{U}$. Fixing on one such retraction pair as above, makes $\mathbf{U}$ also into a model of the $\lambda$-calculus. Whether different retractions give essentially different models I do not know. But the point of the remark is to show that domains can contain their own function spaces for a variety of interesting reasons. ■

**Lean 4**

- [InformationSystems/SomeDomainEquations/Factoid83.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/Basic.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/Basic.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/BasicInst33.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/BasicInst33.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/BasicInst35.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/BasicInst35.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/BasicInst39.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/BasicInst39.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/IsUToken.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/IsUToken.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/UCon.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/UCon.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/UCon_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/UCon_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/UCon_insert_of_ent.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/UCon_insert_of_ent.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/UCon_singleton.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/UCon_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/UCon_subset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/UCon_subset.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/UEnt.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/UEnt.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/UEnt_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/UEnt_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/UEnt_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/UEnt_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/UEnt_trans.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/UEnt_trans.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/UToken.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/UToken.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VCon.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VCon.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VCon_any.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VCon_any.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VEnt.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VEnt.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VEnt_insert_top_imp.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VEnt_insert_top_imp.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VEnt_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VEnt_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VEnt_of_ent_top.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VEnt_of_ent_top.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VEnt_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VEnt_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VEnt_pairLFinset_of_EntSet.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VEnt_pairLFinset_of_EntSet.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VEnt_pairL_inv.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VEnt_pairL_inv.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VEnt_pairRFinset_of_EntSet.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VEnt_pairRFinset_of_EntSet.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VEnt_pairR_inv.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VEnt_pairR_inv.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VEnt_trans.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VEnt_trans.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/VToken.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/VToken.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/mem_foldr_uForget.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/mem_foldr_uForget.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/mem_uForgetFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/mem_uForgetFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/mem_vPairLFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/mem_vPairLFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/mem_vPairRFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/mem_vPairRFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/not_VEnt_empty_top.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/not_VEnt_empty_top.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/not_VEnt_insert_top_of_ent.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/not_VEnt_insert_top_of_ent.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/not_VEnt_singleton_ne_top.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/not_VEnt_singleton_ne_top.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/not_mem_uForget_top.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/not_mem_uForget_top.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/uBot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/uBot.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/uForget.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/uForget.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/uForgetFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/uForgetFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/uForgetFinset_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/uForgetFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/uForgetFinset_insert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/uForgetFinset_insert.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/uForgetFinset_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/uForgetFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/uForgetFinset_singleton.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/uForgetFinset_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/uForgetInsert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/uForgetInsert.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/uSystem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/uSystem.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vBot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vBot.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_insert_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_insert_pairL.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_insert_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_insert_pairR.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_insert_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_insert_top.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_insert_top.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairLFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_insert_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_insert_pairL.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_insert_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_insert_pairR.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_insert_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_insert_top.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_insert_top.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vPairRFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vRhs.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vRhs.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vRhs_eq_product.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vRhs_eq_product.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vSystem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vSystem.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vTop.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vTop.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vUnfold.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vUnfold.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vUnfold_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vUnfold_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vUnfold_pairL.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vUnfold_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid83/vUnfold_pairR.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid83/vUnfold_pairR.lean)
