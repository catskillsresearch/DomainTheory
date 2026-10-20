# Some domain equations

Having outlined the theory of several domain constructs, the final topic for this paper will be the discussion of the *iteration* of these constructs in giving *recursive*, rather than direct definitions of domains. These recursively defined systems have often been called “reflexive,” because the domains generally contain copies of themselves as a part of their very structure. The way that this self-containment takes place is best expressed by the so-called *domain equations*, which are really isomorphisms that relate the domain as a whole to a combination of domains—usually with the main domain as a component. This description is rough, since recursion equations for domains can be as complex as recursion equations for functions. We will not enter into a full theory of domain equations now but will just review some preliminary examples to illustrate how the new presentation makes the constructions more explicit.

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

*A domain for $\lambda$-claculus.* A lengthy discussion with many references on $\lambda$-calculus models can be found in Longo [1982]. All we wish to remark on here is how the method of construction by solving a domain equation can be fit into the new presentation. What I have added to the previous ideas (that in any case came out of an analysis of finite elements of models) is the general view of information systems. In particular the models obtained this way are *not* lattices—hence, the need for the calculations with Con. I hope that the presentation here makes it clearer how “pure” $\lambda$-calculus models can be related to other domains having other types of structures—for instance, those needed in denotational semantics.

The domain equation we wish to solve is:

$$\mathbf{D} \cong \mathbf{A} + (\mathbf{D} \to \mathbf{D}).$$
We proceed in much the same way we did for $\mathbf{T}$, except we must now put in data objects appropriate to the function space. Here is construction, where again $\Delta$ is chosen outside $D_{\mathbf{A}}$ and $\Delta_{\mathbf{D}} = (\Delta, \Delta)$:

(1) $\Delta_{\mathbf{D}} \in D_{\mathbf{D}}$;

(2) $(X, \Delta) \in D_{\mathbf{D}}$ whenever $X \in D_{\mathbf{A}}$;

(3) $(\Delta, (u, v)) \in D_{\mathbf{D}}$ whenever $u, v \in \mathrm{Con}_{\mathbf{D}}$;

(4) $\emptyset \in \mathrm{Con}_{\mathbf{D}}$;

(5) $u \cup \{\Delta_{\mathbf{D}}\} \in \mathrm{Con}_{\mathbf{D}}$ whenever $u \in \mathrm{Con}_{\mathbf{D}}$;

(6) $\{(X, \Delta) \mid X \in w\} \in \mathrm{Con}_{\mathbf{D}}$ whenever $w \in \mathrm{Con}_{\mathbf{A}}$; and

(7) $\{(\Delta, (u_0, v_0)), \ldots, (\Delta, (u_{n-1}, v_{n-1}))\} \in \mathrm{Con}_{\mathbf{D}}$ provided $u_i, v_i \in \mathrm{Con}_{\mathbf{D}}$ for all $i < n$ and whenever $I \subseteq \{0, \ldots, n-1\}$ and $\bigcup \{u_i \mid i \in I\} \in \mathrm{Con}_{\mathbf{D}}$, then $\bigcup \{v_i \mid i \in I\} \in \mathrm{Con}_{\mathbf{D}}$.

What is different here from the definition of $\mathbf{T}$ is the fact that the concepts $D_{\mathbf{D}}$ and $\mathrm{Con}_{\mathbf{D}}$ are mutually recursive because the data objects are themselves built from consistent sets. The scheme is based on a combination of the sum construct and the function-space construct, but the mutual recursion allows “feedback” to occur.

To complete the definition we have to give the clauses for the inductive definition of entailment. They are:

(8) $u \vdash_{\mathbf{D}} \Delta_{\mathbf{D}}$ always;

(9) $u \cup \{\Delta_{\mathbf{D}}\} \vdash_{\mathbf{D}} Y$ whenever $u \vdash_{\mathbf{D}} Y$;

(10) $\{(X, \Delta) \mid X \in w\} \vdash_{\mathbf{D}} (W, \Delta)$ whenever $w \vdash_{\mathbf{A}} W$;

(11) $\{(\Delta, (u_0, v_0)), \ldots, (\Delta, (u_{n-1}, v_{n-1}))\} \vdash_{\mathbf{D}} (\Delta, (u', v'))$ whenever $\bigcup \{v_i \mid u' \vdash_{\mathbf{D}} u_i\} \vdash_{\mathbf{D}} v'$ and the set on the left is in $\mathrm{Con}_{\mathbf{D}}$.

Obviously these definitions are much shorter if we have a domain in which all sets are consistent, but there are many reasons for retaining the consistency concept throughout. The check that $\mathbf{D}$ is an information system and satisfies the domain equation is mechanical. We cannot detail here how this construction provides a $\lambda$-calculus model.

It is clear that these definitions are constructive, and that, with a suitable Gödel numbering of the data objects, the predicates for consistency and entailment are recursively enumerable. However, the recursion used builds up the predicates by going from less complicated data objects to more complicated ones; therefore, the predicates must be recursive, because, for a certain size data object, the derivation that puts it into the predicate is of a bounded length. This observation helps in the discussion of the computability of the operators defined on these domains—another topic we cannot discuss here. $\blacksquare$
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

*A domain of domains.* Not many details can be presented here, but we would also like to remark that even domains can be made into a domain. One way of getting an idea of how this is possible is to note that since subdomains of $\mathbf{U}$ correspond to certain kinds of functions on $\mathbf{U}$, and since the function space of $\mathbf{U}$ is also a subdomain of $\mathbf{U}$, it might be suspected that the subdomains of $\mathbf{U}$ form a single subdomain of $\mathbf{U}$.

That is a fairly sophisticated way of reaching the conclusion (and many details have to be worked out). A more elementary approach would be just to ask what it means to give a finite amount of information about a domain. For the sake of uniformity, suppose that the data objects of the possible domain are drawn from the non-negative integers, and that we conventionally use $0$ for $\Delta$. Then to give a finite amount of information about a domain is—roughly—to specify a finite part of $\mathrm{Con}$ and a finite part of $\vdash$. To make the formulation easier, we will reserve for $1$ a rôle like the one recently played by $\nabla$. What the specifications will boil down to is pairs $(u, v)$ of finite sets of integers used as data objects to convey one piece of information about an entailment relation.

But hold, entailment relations are very closely connected to approximable mappings. Indeed, we remarked before that the identity function as an approximable mapping on a domain is just represented as the underlying entailment relation itself. Suppose we take as our domain the domain of all sets of integers. It is a powerset, so call it $\mathbf{P}$. That is to say, the integers are the data objects, all finite sets are consistent, and the entailment relation is the minimal possible one. (As far as elements go, an arbitrary set of integers is equal to the union of all its finite subsets, which means that the elements of the domain are in a one-one correspondence with the arbitrary sets of integers.) The question is: which approximable mappings on $\mathbf{P}$ into itself correspond to entailment relations on the integers as data objects?

The answer can be expressed most succinctly using our standard notation. If we think of $r : \mathbf{P} \to \mathbf{P}$ as a relation between finite sets in the usual way, then to say that $r$ is reflexive is to say:

(1) $I_{\mathbf{P}} \subseteq r$.

To say that $r$ is transitive is to say:

(2) $r \circ r = r$.
To say that for $r$ the object $0$ plays at being $\Delta$ is to say:

$$(3) \quad \bar{0} \subseteq r(\bot),$$

where in general $\bar{n}$ is short for $\{n\}$ in the domain $\mathbf{P}$. Then, to say that $1$ plays at being a rogue object is to say:

$$(4) \quad \top = r(\bar{1}).$$

Finally, to say that $1$ is an inconsistent object that has to be excluded is to say:

$$(5) \quad \bar{1} \not\subseteq r(\bar{0}).$$

That's it. The collection of approximable mappings satisfying (1)–(5) gives us all the entailment relations we need. Condition (5) is a consistency condition, and for $r$ the consistent finite sets $u$ are those such that $\bar{1} \not\subseteq r(\bar{u})$. What we are asserting is that the totality of $r$ satisfying (1)–(5) forms the elements of a domain—one that has been derived from $(\mathbf{P} \to \mathbf{P})$ in a way similar to the way we derived $\mathbf{U}$ from $\mathbf{V}$ above.

Having made domains into a domain, the next step is to see how constructs on domain (i.e. functors) can be made into approximable mappings. But the retelling and development of that story will have to wait for another publication along with the very interesting chapter on powerdomains. I only hope the ground covered here makes the theory of domains seem more elementary and more natural. ■

**Lean 4**

- [InformationSystems/SomeDomainEquations/DomainEquation.lean](DomainTheory/InformationSystems/SomeDomainEquations/DomainEquation.lean)
- [InformationSystems/SomeDomainEquations/Factoid81.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/Basic.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/Basic.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_atom_con_of_atoms.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon_atom_con_of_atoms.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_atoms_empty_of_right.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon_atoms_empty_of_right.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_insert_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_insert_of_ent.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon_insert_of_ent.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_pairL_of_right.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon_pairL_of_right.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_pairR_of_right.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon_pairR_of_right.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_pairs_empty_of_left.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon_pairs_empty_of_left.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_singleton.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeCon_subset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeCon_subset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEnt.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeEnt.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload_of_no_atoms_no_pairs.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload_of_no_atoms_no_pairs.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload_trans.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeEntPayload_trans.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEnt_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeEnt_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeEnt_trans.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeEnt_trans.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/TreeToken.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/TreeToken.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_pairL.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_pairR.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset_insert_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_pairL.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_pairR.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomFinset_singleton_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/atomInsert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/atomInsert.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/eq_singleton_bot_of_subset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/eq_singleton_bot_of_subset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/mem_atomFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/mem_atomFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/mem_foldr_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/mem_foldr_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/mem_pairLFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/mem_pairLFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/mem_pairRFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/mem_pairRFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_pairL.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_pairR.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_insert_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_pairL.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_pairR.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairLFinset_singleton_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairL_ne_or_subset_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairL_ne_or_subset_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_pairL.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_pairR.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_insert_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_pairL.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_pairR.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairRFinset_singleton_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/pairR_ne_or_subset_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/pairR_ne_or_subset_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeBot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/treeBot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeRhs.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/treeRhs.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeRhs_eq_sum_product.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/treeRhs_eq_sum_product.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeSystem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/treeSystem.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/treeUnfold.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_pairL.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_pairL.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_pairL_bot_eq_pairR_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_pairL_bot_eq_pairR_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_pairR.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid81/treeUnfold_pairR.lean)
- [InformationSystems/SomeDomainEquations/Factoid82.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/Basic.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/Basic.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/BasicInst23.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/BasicInst23.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/BasicInst27.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/BasicInst27.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/BasicInst70.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/BasicInst70.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/BasicInst74.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/BasicInst74.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/IsLamToken.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/IsLamToken.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/IsLamWF.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/IsLamWF.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/IsLamWF_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/IsLamWF_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamCon.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamCon.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_funion_of_entSet.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_funion_of_entSet.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_insert_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_insert_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_insert_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_insert_of_ent.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_insert_of_ent.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_of_fun_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_of_fun_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_of_fun_nonempty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_of_fun_nonempty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_singleton_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_singleton_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_singleton_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_singleton_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_singleton_funTok.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConDepth_singleton_funTok.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_FunCon_mono_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_FunCon_mono_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_atom_con.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_atom_con.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_atom_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_atom_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_down_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_down_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_exists_FunCon.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_exists_FunCon.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_fun_FunCon_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_fun_FunCon_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_fun_FunCon_right.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_fun_FunCon_right.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_fun_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_fun_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_fun_wf.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_fun_wf.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_insert_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_insert_of_ent_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_insert_of_ent_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_insert_of_ent_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_insert_of_ent_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamConN_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamConN_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamCon_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamCon_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamCon_of_forget_singleton.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamCon_of_forget_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamCon_singleton_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamCon_singleton_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamCon_singleton_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamCon_singleton_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamCon_singleton_funTok.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamCon_singleton_funTok.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamCon_subset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamCon_subset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDCon.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDCon.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDCon_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDCon_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDCon_insert_of_ent.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDCon_insert_of_ent.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDCon_listToLamDFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDCon_listToLamDFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDCon_singleton.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDCon_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDCon_subset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDCon_subset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDEnt.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDEnt.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDEnt_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDEnt_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDEnt_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDEnt_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDEnt_trans.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDEnt_trans.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamDToken.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamDToken.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEnt.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEnt.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepthInst10.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepthInst10.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepthInst17.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepthInst17.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepthInst18.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepthInst18.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepthInst31.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepthInst31.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepthInst9.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepthInst9.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_con.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_con.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_trans.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_trans.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_weaken_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_weaken_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_weaken_fun.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_weaken_fun.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_weaken_insert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntDepth_weaken_insert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntN.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntN.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntN_con.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntN_con.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntN_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntN_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEntN_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEntN_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEnt_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEnt_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEnt_con.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEnt_con.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamEnt_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamEnt_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamToken.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamToken.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamTokenCon.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamTokenCon.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamTokenCon_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamTokenCon_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamTokenCon_singleton.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamTokenCon_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamTokenCon_subset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamTokenCon_subset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamTokenEnt.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamTokenEnt.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamTokenEnt_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamTokenEnt_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/LamTokenEnt_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/LamTokenEnt_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/RawLamToken.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/RawLamToken.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/filter_ne_subset_of_subset_insert_lam.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/filter_ne_subset_of_subset_insert_lam.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_funion_le.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_funion_le.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_inputUnion_lt.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_inputUnion_lt.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_insert_le.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_insert_le.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_listToFinset_le.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_listToFinset_le.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_list_lt_funTok.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_list_lt_funTok.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_list_lt_funTok_out.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_list_lt_funTok_out.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_of_mem_funTok.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_of_mem_funTok.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_outputUnion_lt.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/finsetMaxDepth_outputUnion_lt.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/foldl_list_le_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/foldl_list_le_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/foldl_max_ge_init.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/foldl_max_ge_init.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/foldl_max_mono_init.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/foldl_max_mono_init.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/foldr_max_le_of_forall.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/foldr_max_le_of_forall.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/foldr_max_lt_of_forall.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/foldr_max_lt_of_forall.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/funion_assoc_lam.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/funion_assoc_lam.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/funion_comm_lam.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/funion_comm_lam.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/funion_empty_right_lam.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/funion_empty_right_lam.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/insert_filter_ne_lam.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/insert_filter_ne_lam.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_funion.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_funion.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_insert_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_insert_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_insert_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_insert_funTok.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_insert_funTok.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_singleton_funTok.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamAtomFinset_singleton_funTok.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamAtomInsert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamAtomInsert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamBot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamBot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamDBot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamDBot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamDForget.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamDForget.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamDForgetFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamDForgetFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamDForgetFinset_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamDForgetFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamDForgetFinset_insert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamDForgetFinset_insert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamDForgetFinset_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamDForgetFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamDForgetFinset_singleton.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamDForgetFinset_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamDForgetInsert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamDForgetInsert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamDForget_listToLamDFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamDForget_listToLamDFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamForget.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamForget.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamForgetFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamForgetFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamForgetFinset_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamForgetFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamForgetFinset_insert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamForgetFinset_insert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamForgetFinset_singleton.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamForgetFinset_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamForgetInsert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamForgetInsert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_funion.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_funion.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_insert_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_insert_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_insert_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_insert_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_insert_funTok.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_insert_funTok.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_mono.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_mono.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_singleton_funTok.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamFunFinset_singleton_funTok.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamFunInsert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamFunInsert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamInUnionInsert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamInUnionInsert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamInputUnion.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamInputUnion.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamInputUnion_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamInputUnion_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamInputUnion_funion.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamInputUnion_funion.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamInputUnion_insert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamInputUnion_insert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamInputUnion_singleton.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamInputUnion_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamOutUnionInsert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamOutUnionInsert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamOutputUnion.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamOutputUnion.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamOutputUnion_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamOutputUnion_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamOutputUnion_funion.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamOutputUnion_funion.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamOutputUnion_insert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamOutputUnion_insert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamOutputUnion_singleton.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamOutputUnion_singleton.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamRhs.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamRhs.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamRhs_eq_sum_function.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamRhs_eq_sum_function.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamUnfold.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamUnfold.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamUnfold_atom.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamUnfold_atom.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lamUnfold_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lamUnfold_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lambdaSystem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lambdaSystem.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/lambdaSystem_con_axioms.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/lambdaSystem_con_axioms.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/le_finsetMaxDepth_of_mem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/le_finsetMaxDepth_of_mem.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/listToFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/listToFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/listToLamDFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/listToLamDFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/maxDepthInsert.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/maxDepthInsert.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/max_le_max_nat.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/max_le_max_nat.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/mem_foldr_lamDForget.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/mem_foldr_lamDForget.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/mem_lamAtomFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/mem_lamAtomFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/mem_lamDForgetFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/mem_lamDForgetFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/mem_lamForgetFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/mem_lamForgetFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/mem_lamFunFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/mem_lamFunFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/mem_lamInputUnion.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/mem_lamInputUnion.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/mem_lamOutputUnion.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/mem_lamOutputUnion.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/mem_listToFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/mem_listToFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/mem_listToLamDFinset.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/mem_listToLamDFinset.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/rawDepth.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/rawDepth.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/rawDepth_funTok_gt_left.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/rawDepth_funTok_gt_left.lean)
- [InformationSystems/SomeDomainEquations/Factoid82/rawDepth_funTok_gt_right.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid82/rawDepth_funTok_gt_right.lean)
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
- [InformationSystems/SomeDomainEquations/Factoid84.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/Basic.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/Basic.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/BotApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/BotApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/BotApprox_any.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/BotApprox_any.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/ConsistentApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/ConsistentApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/DomainApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/DomainApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/IdemApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/IdemApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/IsDomainApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/IsDomainApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/P.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/P.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/PEnt.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/PEnt.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/P_AllConsistent.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/P_AllConsistent.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/ReflApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/ReflApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/RogueApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/RogueApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/bar.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/bar.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/barElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/barElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/barElement_zero_eq_bot.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/barElement_zero_eq_bot.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/botElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/botElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatDomainApprox.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatDomainApprox.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatMap.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_consistent.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatMap_consistent.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_idem.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatMap_idem.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_isDomain.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatMap_isDomain.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_refl.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatMap_refl.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_rogue.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatMap_rogue.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatMap_toElement_of_mem_one.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatMap_toElement_of_mem_one.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatRel.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatRel.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatRel_empty.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatRel_empty.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/flatRel_of_mem_one.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/flatRel_of_mem_one.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/mem_barElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/mem_barElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/mem_botElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/mem_botElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/mem_topElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/mem_topElement.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/not_RogueApprox_idMap.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/not_RogueApprox_idMap.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/scottCon.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/scottCon.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/scottCon_empty_iff_consistent.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/scottCon_empty_iff_consistent.lean)
- [InformationSystems/SomeDomainEquations/Factoid84/topElement.lean](DomainTheory/InformationSystems/SomeDomainEquations/Factoid84/topElement.lean)
