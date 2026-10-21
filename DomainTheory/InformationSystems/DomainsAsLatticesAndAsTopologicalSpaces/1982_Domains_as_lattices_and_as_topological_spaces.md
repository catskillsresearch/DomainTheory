# Domains as lattices and as topological spaces

I will attempt to keep this section as informal as possible—especially as Sections 2 and 3 were quite formal (i.e. mathematical) enough. The main purpose of the discussion of this section is to relate the new presentation of the Theory of Domains to previously published ones. (Some alternatives are discussed at the end of the paper.)

*Lattice-theoretic considerations.* Let $\mathbf{A}$ be an information system. Because the elements of $|\mathbf{A}|$ are introduced as sets, these elements can be given structure from what we know already about ordinary sets. For instance, the set-theoretic inclusion relation between sets can certainly be applied to elements. The question is: What does $x \subseteq y$ mean intuitively? In fact, we have already mentioned this relationship before. It means that every proposition (among the ones given by the information system) true of $x$ is also true of $y$ (though not necessarily conversely). In other words, $x$ is perhaps only partially determined, while $y$ is more fully determined in a way that includes everything true of $x$. Clearly, then, if we grant the interest of partial elements, then this relation is a natural and basic one. We often read "$x \subseteq y$" as "$x$ approximates $y$".

Now here is one of the main points of the new exposition: Because $x \subseteq y$ is *defined* in terms of a familiar mathematical notion, then as a relation between elements it inherits all the well-known properties of the set-theoretical relation. It should not be necessary to write them out, for everyone who can read this far knows that $\subseteq$ is in particular reflexive and transitive. We say that the domain $|\mathbf{A}|$ is a *partially ordered set under inclusion*. We note that this (trivial) result is *proved* from the definition rather than assumed as an axiom.

Let us try out another notion. Elements are consistent, deductively closed sets of data objects. Right? Every subset of a consistent set is consistent, but not every subset is closed under entailment, in general. Right? But suppose that $x$ and $y$ are two elements. It can easily be seen that their intersection $x \cap y$ is again consistent and deductively closed (by a 2 nanosecond proof). Therefore, the set of elements of a domain is closed under intersection. This means that, as a partially ordered set, $|\mathbf{A}|$ is an *inf semilattice*.

Well, the exact terminology is quite unimportant, but the properties of $\cap$ when combined with the properties of $\subseteq$ are pleasantly "algebraic" (and run to several lines when written out). We all know them: $\cap$ is idempotent, commutative, and associative. The element $\bot$, being the
The element $\bot$, being the smallest element of the domain, is a zero element for $\cap$. The operation $\cap$ is monotonic with respect to $\subseteq$, and we have the connection:

$$x \subseteq y \text{ iff } x \cap y = x.$$

What has just been alluded to in words is the standard mathematical axiomatization of the properties of an infimum (or meet) operation in a partially ordered set. (Remember, however, to have an operation well defined within a set it is necessary also to have closure under that operation.)

What about infs of subsets? No problem. For any *non-empty* subfamily of $|\mathbf{A}|$, it is just as easy to prove that the set-theoretical intersection of all the elements in the subfamily is again an element of the domain. This makes $|\mathbf{A}|$ a (conditionally) complete inf semilattice. Even if you do not have any idea what I am talking about, it does not matter because the properties of the domain are built in by the very definition; you do not have to worry *at the start* about their formulation, for you can prove them when you need them (if ever).

What about suprema (or sups or joins)? Here there is a slight problem, because in the way we set things up they *do not* always have to exist. Consider what happens with just two elements $x$ and $y$. The set-theoretical union of the two elements as subsets of $D_{\mathbf{A}}$ need be neither consistent nor deductively closed; and even if $x \cup y$ is consistent, it need not be closed under entailment. So if we want sups *within* $|\mathbf{A}|$, we cannot get by as cheaply as we can with a domain of arbitrary sets for which the simple union is the answer.

Let us write the sup (supposing it exists in $|\mathbf{A}|$) as $x \sqcup y$. What do we have when we actually have it? By the lore of partially ordered sets, $x \sqcup y$ must be the *least element* in $|\mathbf{A}|$ which includes (in the sense of $\subseteq$) both $x$ and $y$. Now we have just spoken about infs of families of elements: they exist if the family is non-empty. This indicates that $x \sqcup y$ exists exactly when there is at least one element $z$ in $|\mathbf{A}|$ such that $x \subseteq z$ and $y \subseteq z$. This turns out to be a way to say—entirely inside $|\mathbf{A}|$—that $x \cup y$ is consistent. In other words (and more generally) a sup of a subfamily exists if, and only if, the union of the family is consistent. (And in that case the sup is just the deductive closure of the union—that is, it is generally larger than the simple set-theoretical union.) This has an axiomatic version, but it is slightly complicated by the fact that sups do not always exist. In case $\top_{\mathbf{A}}$ exists, then we always have all the sups, and $|\mathbf{A}|$ is a *complete lattice*. (This is discussed in full axiomatic splendor in Gierz, et al. [1980].) But, let it hasten to be added, not every complete lattice is isomorphic to a domain. The lattices that correspond to domains are the so-called *algebraic lattices*. (See the discussion loc. cit. for the additional axiomatics required.) When the top is missing, the partially ordered structures corresponding to domains are called *conditionally complete, algebraic cpo's*.

There is, however, an important case in $|\mathbf{A}|$ where the union is consistent and is, in fact, the sup in the domain. Suppose we have a sequence of elements such that

$$x_0 \subseteq x_1 \subseteq x_2 \subseteq \cdots \subseteq x_n \subseteq x_{n+1} \subseteq \cdots$$

As $n$ increases, we can say that the elements $x_n$ are getting “better and better”; thus, they must be approaching something even more desirable *in the limit*. Let

$$y = \bigcup_{n=0}^{\infty} x_n,$$
then there is no question that $y$ is a subset of $D_{\mathbf{A}}$. But is it an element? Consistency, recall, means that every *finite* subset is in $\mathrm{Con}_{\mathbf{A}}$. The trick is that a finite subset of $y$ must be a subset of one of the $x_n$, because the sequence of elements $x_n$ is increasing. But all the terms of our given sequence are elements, and so, consistent; therefore, every finite subset of $y$ is consistent.

The same argument also shows that the set $y$ of data objects is closed under entailment, because $\vdash_{\mathbf{A}}$ is defined as a relation between finite (consistent) sets and data objects. It follows that since each $x_n$ is a set closed under $\vdash_{\mathbf{A}}$, then so is $y$. In other words, $y$ is indeed an element. Otherwise said, the domain $|\mathbf{A}|$ is closed under the formation of unions of increasing chains of elements, and the union is, of course, the sup in the sense of the partial ordering. Again we have proved closure rather than assuming it, and the necessary properties of the sup follow from its definition as a union.

This last argument can be generalized—as is well known to mathematicians—to the case of *directed* families of elements. The word "directed," or better "upward-directed," means that every finite number of elements in the family is included in some further element of the family; chains always have this property. A good example of the use of directed sets of elements figures in the discussion of the *finite elements* of the domain.

As we have remarked several times, any consistent set of data objects *generates* an element by closing it up under the entailment relation; thus, in particular, any set $u \in \mathrm{Con}$ generates an element. Let us write

$$\overline{u} = \{X \in D_{\mathbf{A}} \mid u \vdash_{\mathbf{A}} X\}$$

for the *closure* of $u$ under entailment. (This notation could be used for any consistent subset of $D_{\mathbf{A}}$, but the case of finitely generated elements is especially important.) Such a $\overline{u}$ is always an element of $|\mathbf{A}|$; the totality of such elements form, by definition, the *finite elements* of the domain. The notation $\overline{u}$ should of course be decorated with a subscript $\mathbf{A}$, but, as there is no good place to write it in, we leave it out.

We have for all elements $x$ of the domain the basic formula:

$$x = \bigcup \{\overline{u} \mid u \in \mathrm{Con}_{\mathbf{A}} \text{ and } u \subseteq x\}.$$

This can be read intuitively as saying that every element of the domain is the *limit* of its *finite approximations*. And, having used the word "limit" so often, we ought now to say something about how to make the meaning of this word correct mathematically. Note that in the limit representation for $x$, the union is a directed one. (Why?)

*Topological considerations.* Geometrically speaking, a topological space is a collection of "points" which group themselves in various "neighborhoods" providing thereby a sense of "nearness." More specifically, a neighborhood of a point in a *metric space* consists of all those points within a certain positive "distance" from the given point; that is, nearness is limited, but it is not pushed to *zero*. The major reason for leaving some "breathing space" around the point comes out in defining continuity of functions.

A function $f$ from one topological space to another is said to be *continuous* provided that, for every point $x$ of the first space, and for every neighborhood in the second space around $f(x)$, it is
possible to find—in the first space—a neighborhood around $x$ with the following property. If the function is restricted to this neighborhood, then its values lie entirely in the given neighborhood around $f(x)$. In the metric case we can say that if we do not want the function to wander any great distance from $f(x)$, then there is a restricted distance around $x$ giving a neighborhood over which the function values stay as close to $f(x)$ as specified. This keeps the function from jumping around wildly, since small variations in $x$ lead to only small variations in $f(x)$.

The intuition about continuity is no doubt very clear in the more geometric examples, and geometric intuition can carry us quite far. But the spaces obtained from domain theory are not really geometric spaces, so we need to make some shifts in our metaphors. The geometric notion of a point usually implies that two points are perfectly distinguishable: if $x$ and $y$ are different, then they have disjoint neighborhoods. This is certainly true in the metric case, where, if two points are different, then they are at a positive distance apart. Early on in the study of topological spaces, however, it was found that not all spaces were metric, and weaker separation properties of pairs of distinct points were uncovered. One of the very weak versions of such a condition is called the "$T_0$-axiom." The best way to put it is that if two points have the same neighborhoods, then they are the same. The contrapositive statement sounds odd: if two points are distinct, then there is a neighborhood that contains one but not the other. The oddity of this statement lies in the feeling that you cannot make up your mind over which is the better point.

In our domains there is already a notion of "betterness" which proves to be very closely related to the implicit neighborhood structure. The reason why our domains, as spaces of points, are not "geometric" in the familiar sense is that they contain partial elements. A geometric point, on the other hand, is "perfect" or totally determined; it cannot be made better than it already is. The metric in common spaces is measuring something other than betterness, for there are competing notions of approximation afoot here. Thus, we must keep our special goals in defining domains clearly in mind to avoid confusion.

Consider an information system $\mathbf{A}$. For each $u \in \mathrm{Con}_{\mathbf{A}}$, we define a corresponding neighborhood of $|\mathbf{A}|$ by the equation:

$$[u]_{\mathbf{A}} = \{x \in |\mathbf{A}| \mid u \subseteq x\}.$$

The neighborhoods of an element $x$ are all those sets $[u]_{\mathbf{A}}$, where $u \subseteq x$. Note that this is the same as saying $\overline{u} \subseteq x$ or $\overline{u}$ approximates $x$. Indeed, the neighborhoods are in a one-one correspondence with the finite elements of $|\mathbf{A}|$. A neighborhood collects together all those elements sharing the same finite amount of information.

If both $u \subseteq x$ and $v \subseteq x$, then it is easy to see that the intersection of the two neighborhoods is again a neighborhood of $x$ by virtue of the formula:

$$[u]_{\mathbf{A}} \cap [v]_{\mathbf{A}} = [u \cup v]_{\mathbf{A}}.$$

In case $u$ and $v$ are inconsistent with each other, then the intersection will be the empty set $\emptyset$. Because every element of our domain $|\mathbf{A}|$ is the union of the finite elements it contains, it is trivial to prove that two elements with exactly the same neighborhoods are the same. For these reasons, then, it follows that $|\mathbf{A}|$ is a $T_0$-topological space. The immediate reaction to this intelligence is: So what?

The answer to this scepticism will appear in the best light when we discuss in the next section the notion of function or mapping appropriate to our domains. The argument will be based on the
extremely elementary form of the definition that characterizes the general continuous function together with the fact that the geometric intuition is suggestive of theorems to prove. In Section 6 we will find that the space of all continuous functions between two given domains is also a domain, a most useful result that is interesting topologically. But further interest for Domain Theory comes from the circumstance that there is a connection between geometry and domains. We cannot go into the full details here, but I can make some brief remarks.

Before continuing that discussion, though, it should be remarked that once the topology of the domain has been uncovered, then the unions of chains of elements (or directed sets of elements) are topological limits according to accepted general definitions. Thus, what we felt intuitively was a limiting process (the getting better and better up to the union) is in fact a limit formation in a precise mathematical sense. This helps convince us that we are on the right track.

*Total elements as a space.* In any domain it can be proved that any element $x$ can be extended to a *total element* $t$, which is characterized by the property that it is a *maximal* element of the partial ordering. (Perhaps there are many such $t$, but there is always at least one with $x \subseteq t$.) Recall that the set of all total elements of $|\mathbf{A}|$ is denoted by $\mathrm{Tot}_{\mathbf{A}}$. Because the set $\mathrm{Tot}_{\mathbf{A}} \subseteq |\mathbf{A}|$, it is a topological space itself. Suppose $s$ and $t$ are two distinct total elements, then they must be inconsistent with each other—but we shall prove more. If every finite consistent $u \subseteq s$ also satisfied $u \subseteq t$, then $s \subseteq t$ would follow. But this is impossible, because $s$ is maximal. Let, then, $u \in \mathrm{Con}_{\mathbf{A}}$ with $u \subseteq s$ be chosen so that $u \subseteq t$ fails. Now $u$ must be inconsistent with $t$, since otherwise there would be an element containing them both. It follows that $u$ must be inconsistent with some $v \in \mathrm{Con}_{\mathbf{A}}$ with $v \subseteq t$. In this way we show that the neighborhoods $[u]_{\mathbf{A}}$ and $[v]_{\mathbf{A}}$ are disjoint.

This argument proves that $\mathrm{Tot}_{\mathbf{A}}$ is a *Hausdorff space* (or $T_2$-space). We cannot go further into the details here, but it is also a totally disconnected, compact Hausdorff space. (These spaces—well known from studies of Logic and the Theory of Boolean Algebras—are also zero-dimensional.) Assuming the countability of $\mathrm{Con}_{\mathbf{A}}$, which is not such a bold assumption, all such spaces can be conveniently embedded into the real line so as to preserve the topological structure. Perhaps this does not seem so surprising, but it shows that the topological nature of $\mathrm{Tot}_{\mathbf{A}}$, the uppermost level of the $T_0$ space $|\mathbf{A}|$, is indeed quite geometric. And it can also be shown that any arbitrary continuous function on $\mathrm{Tot}_{\mathbf{A}}$ into *any* topological space can be extended to a continuous function on $|\mathbf{A}|$, so the whole domain proves to be quite a "roomy" space with many good connections to more usual topological spaces.

*A note on neighborhood structures.* Topological spaces can be defined in several ways, and in general they do not carry a preferred neighborhood structure. (For example, there is no topological significance to the usual rational intervals we use to define neighborhoods for the real line: any similarly dense set of points would do in place of the rational numbers.) Domains, the way we have defined them, however, do have preferred neighborhoods. The set of finite elements of $|\mathbf{A}|$ can be defined topologically, and as we have seen they determine a convenient set of neighborhoods. (The reason for all this is the so-called zero-dimensional character of the domains. There is a higher-dimensional theory, but this leads to continuous lattices and can only be explained using the kind of presentation in Gierz, *et al.* [1980]. It is too long-winded a story for the present paper. The higher-dimensional domains do not have a preferred set of neighborhoods, however.)

Having realized this, it is a short step to giving an algebraic axiomatization of the neighborhood structure. Smyth [1975] contains a presentation in terms of the equivalent notion of

**Lean 4**

- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41.lean](Factoid41.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/Basic.lean](Factoid41/Basic.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/botElement_inf.lean](Factoid41/botElement_inf.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/inf.lean](Factoid41/inf.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/inf_assoc.lean](Factoid41/inf_assoc.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/inf_botElement.lean](Factoid41/inf_botElement.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/inf_comm.lean](Factoid41/inf_comm.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/inf_idem.lean](Factoid41/inf_idem.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/inf_le_iff.lean](Factoid41/inf_le_iff.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/inf_le_left.lean](Factoid41/inf_le_left.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/inf_le_right.lean](Factoid41/inf_le_right.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/inf_mono.lean](Factoid41/inf_mono.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/le_iff_inf_eq.lean](Factoid41/le_iff_inf_eq.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid41/le_inf.lean](Factoid41/le_inf.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid42.lean](Factoid42.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid42/Basic.lean](Factoid42/Basic.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid42/familyInf.lean](Factoid42/familyInf.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid42/familyInfCarrier.lean](Factoid42/familyInfCarrier.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid42/familyInf_le.lean](Factoid42/familyInf_le.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid42/familyInf_le_iff.lean](Factoid42/familyInf_le_iff.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid42/familyInf_pair.lean](Factoid42/familyInf_pair.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid42/le_familyInf.lean](Factoid42/le_familyInf.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43.lean](Factoid43.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/Basic.lean](Factoid43/Basic.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/IsFinitelyConsistent.lean](Factoid43/IsFinitelyConsistent.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/deductiveClosure.lean](Factoid43/deductiveClosure.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/exists_entSet_of_subset_deductive.lean](Factoid43/exists_entSet_of_subset_deductive.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/exists_isLUB_iff.lean](Factoid43/exists_isLUB_iff.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/exists_join_iff.lean](Factoid43/exists_join_iff.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/familySup.lean](Factoid43/familySup.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/familySup_le.lean](Factoid43/familySup_le.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/familyUnionCarrier.lean](Factoid43/familyUnionCarrier.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/finitelyConsistent_of_upperBound.lean](Factoid43/finitelyConsistent_of_upperBound.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/join.lean](Factoid43/join.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/join_le.lean](Factoid43/join_le.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/le_familySup.lean](Factoid43/le_familySup.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/le_join_left.lean](Factoid43/le_join_left.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/le_join_right.lean](Factoid43/le_join_right.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/subset_deductiveClosure.lean](Factoid43/subset_deductiveClosure.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44.lean](Factoid44.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/Basic.lean](Factoid44/Basic.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/IsChain.lean](Factoid44/IsChain.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/IsDirected.lean](Factoid44/IsDirected.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/IsDirected_of_IsChain.lean](Factoid44/IsDirected_of_IsChain.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/chainSup.lean](Factoid44/chainSup.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/directedSup.lean](Factoid44/directedSup.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/directedSup_carrier_eq_union.lean](Factoid44/directedSup_carrier_eq_union.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/directedSup_le.lean](Factoid44/directedSup_le.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/exists_mem_of_subset_directedUnion.lean](Factoid44/exists_mem_of_subset_directedUnion.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/finitelyConsistent_of_directed.lean](Factoid44/finitelyConsistent_of_directed.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/le_directedSup.lean](Factoid44/le_directedSup.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid45.lean](Factoid45.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid45/Basic.lean](Factoid45/Basic.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid45/botElement_eq_closure_empty.lean](Factoid45/botElement_eq_closure_empty.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid45/compact_closure.lean](Factoid45/compact_closure.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid45/directed_finiteApproximants.lean](Factoid45/directed_finiteApproximants.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid45/eq_directedSup_finiteApproximants.lean](Factoid45/eq_directedSup_finiteApproximants.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid45/finiteApproximants.lean](Factoid45/finiteApproximants.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid45/nonempty_finiteApproximants.lean](Factoid45/nonempty_finiteApproximants.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46.lean](Factoid46.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/Basic.lean](Factoid46/Basic.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/ScottContinuous.lean](Factoid46/ScottContinuous.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/basicOpen.lean](Factoid46/basicOpen.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/basicOpen_inter.lean](Factoid46/basicOpen_inter.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/eq_of_basicOpen_eq.lean](Factoid46/eq_of_basicOpen_eq.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/mem_basicOpen.lean](Factoid46/mem_basicOpen.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/mono.lean](Factoid46/mono.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/ofScottContinuous.lean](Factoid46/ofScottContinuous.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/toElement_directedSup.lean](Factoid46/toElement_directedSup.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/toElement_ofScottContinuous.lean](Factoid46/toElement_ofScottContinuous.lean)
- [InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/toScottContinuous.lean](Factoid46/toScottContinuous.lean)
