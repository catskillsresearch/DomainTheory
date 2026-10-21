# Definition 3.1

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
