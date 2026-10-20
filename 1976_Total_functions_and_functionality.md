# Total functions and functionality

There is an inevitable conflict between the concepts of *total* and *partial* functions: we desire the former, but it is the latter we usually get. Total functions are better because they are “well-defined” at all their arguments, but the rub is that there is no general way of deciding when a *definition* is going to be well-defined in all its uses. In analysis we have singularities, and in recursion theory we have endless, nonfinishing computations. In the present theory we have in effect evaded the question in two ways. First we have embraced the partial function as the norm. But secondly, and possibly confusingly, the multiple-valued functions are normal, total functions from $\mathbf{P}\omega$ into $\mathbf{P}\omega$. The point, of course, is that we are making a *model* of the partial functions in terms of ordinary mathematical functions. But note that the success of the *model* lies in *not* using arbitrary functions: it is only the continuous functions that correspond to the kind of partial functions we wanted to study. It would be a mistake to think of the variables in $\lambda$-calculus as ranging over arbitrary functions—and this mistake was made by both Church and Curry. The fixed-point operator **Y** shows that we must restrict attention to functions which do have fixed points. It is certainly the case that $\mathbf{P}\omega$ is not the only model for the $\lambda$-calculus, but it is a very satisfactory model and is rich enough to illustrate what can and what cannot be done with partial functions.

Whatever the pleasures of partial functions (and the multiple-valued ones, too), the desire for total functions remains. Take the integers. We are more interested in $\omega$ than $\omega \cup \{\bot, \top\}$. Since the multiple values $\bot$ and $\top$ are but two in number, it is easy to avoid them. The problem becomes tiresome in considering functions, however. The lattice represented by the retract $\mathbf{int} \circ\to \mathbf{int}$ is much too large, in that there are as many nontotal functions in this domain as total ones. The aim of the present section is to introduce an interpretation of a theory of functionality in the model $\mathbf{P}\omega$ that provides a convenient way of restricting attention to the functions (or other objects) that are total in the desired sense. The theory of functionality is rather like proposals of Curry, but not quite the same for important reasons as we will see.

In the theory of retracts of §§ 5 and 6, the plan of “restricting attention” was the very simple one of restricting to a *subset*. It was made notationally simple as the subsets in question could be parameterized by continuous functions. The retraction mappings stand in for their ranges. Even better, certain continuous functions act on these retractions as space-forming functors (such as $\oplus$ and $\circ\to$), which gives greater notational simplicity because one language is able to serve for several tasks. When we pass to the theory of total functions, this same kind of simplicity is no longer possible owing to an increase in quantifier complexity in the necessary definitions. (This remark is made definite below.) Another point where there is some loss of simplicity concerns the representation of entities in $\mathbf{P}\omega$: subsets will no longer be enough, since we will need *quotients* of subsets. This is not a very startling point. Many constructions are affected in a natural way via equivalence classes. An equivalence relation makes you blind to certain distinctions. It may be easier also to remain a bit blind than to search for the most beautiful representative of an equivalence class: there may be nothing to choose between several candidates, and it can cost too much effort to attempt a choice. Thus our first agreement is that for many purposes a *kind* of object can be taken as a set of equivalence classes for an equivalence relation on a subset of $\mathbf{P}\omega$.

Because $\mathbf{P}\omega$ is closed under the pairing function $\lambda x \lambda y.\, \langle x, y \rangle$, we shall construe relations on subsets of $\mathbf{P}\omega$ as subsets of $\mathbf{P}\omega$ all of whose elements are ordered pairs. That is, a relation $A$ satisfies this inclusion:

$$(7.1) \quad A \subseteq \{\langle x, y \rangle \mid x, y \in \mathbf{P}\omega\}.$$

**DEFINITION.** A (restricted) *equivalence relation* on $\mathbf{P}\omega$ is a symmetric and transitive relation on $\mathbf{P}\omega$.

Such relations are restricted because they are only reflexive on their domains—which are the same as their ranges—and these are the subsets with which the relations are concerned. We shall write $x \, A \, y$ for $\langle x, y \rangle \in A$ and $x : A$ for $x \, A \, x$. What we assume about these relations is the following:

$$(7.2) \quad x \, A \, y \text{ implies } y \, A \, x.$$

$$(7.3) \quad x \, A \, y \text{ and } y \, A \, z \text{ imply } x \, A \, z.$$

In case $a$ is a retract, we introduce an equivalence relation to correspond:

$$(7.4) \quad E_a = \{\langle x, x \rangle \mid x : a\}.$$

This is the identity relation restricted to the range of $a$. Such relations (for obvious reasons) and many others satisfy an additional *intersection property*:

$$(7.5) \quad x \, A \, y \text{ and } x \, A \, z \text{ imply } x \, A \, (y \cap z).$$

We shall not generally assume (7.5) in this short discussion, but it is often convenient.

Each equivalence relation represents a *space*: the space of all its equivalence classes. Such spaces form a category more extensive than the category of retracts studied above. The familiar functors can be extended to this larger category by these definitions:

$$(7.6) \quad A \to B = \{\langle \lambda x.\, u(x), \lambda x.\, v(x) \rangle \mid u(x) \, B \, v(y) \text{ whenever } x \, A \, y\},$$

$$(7.7) \quad A \times B = \{\langle \langle x, x' \rangle, \langle y, y' \rangle \rangle \mid x \, A \, y \text{ and } x' \, B \, y'\},$$

$$(7.8) \quad A + B = \{\langle \langle 0, x \rangle, \langle 0, y \rangle \rangle \mid x \, A \, y\} \cup \{\langle \langle 1, x' \rangle, \langle 1, y' \rangle \rangle \mid x' \, B \, y'\}.$$

**THEOREM 7.1 (The closure theorem).** *If $A$ and $B$ are restricted equivalence relations, then so are $A \to B$, $A \times B$ and $A + B$. We find:*

(i) $f : A \to B$ iff $f = \lambda x.\, f(x)$ and whenever $x \, A \, y$, then $f(x) \, B \, f(y)$, in particular:

(ii) if $f : A \to B$ and $x : A$, then $f(x) : B$; furthermore,

(iii) $u : A \times B$ iff $u = \langle u_0, u_1 \rangle$ and $u_0 : A$ and $u_1 : B$;

(iv) $u : A + B$ iff either $u = \langle 0, u_1 \rangle$ and $u_1 : A$ or $u = \langle 1, u_1 \rangle$ and $u_1 : B$.

It follows easily from (7.1) that the restricted equivalence relations form a Cartesian closed category which—in distinction to the category of retracts—has disjoint sums (or coproducts as they are usually called in category theory). This result is probably a special case of a more general theorem. The point is that $\mathbf{P}\omega$ itself is a space in a Cartesian closed category (that of continuous lattices and continuous maps) and it contains as subspaces the Boolean space and especially its own function space and Cartesian square. In this circumstance any such rich space must be such that its restricted equivalence relations again form a good category. Our construction is not strictly categorical in nature, as we have used the elements of $\mathbf{P}\omega$ and have relied on being able to form arbitrary subsets (arbitrary relations). But a more abstract formulation must be possible. The connection with the category of retracts is indicated in the next theorem.

**THEOREM 7.2 (The isomorphism theorem).** *If $a$ and $b$ are retracts, we have the following isomorphisms and identities relating the spaces:*

(i) $E_a \cong \{\langle x, y \rangle \mid a(x) = a(y)\}$;

(ii) $E_{a \circ\to b} \cong E_a \to E_b$;

(iii) $E_{a \otimes b} = E_a \times E_b$;

(iv) $E_{a \oplus b} = E_a + E_b \cup \{\langle \bot, \bot \rangle, \langle \top, \top \rangle\}$.

Part (iv) is not categorical in nature as it stands, but (ii) and (iii) indicate that $E$ is a functor from the category of retracts into the category of equivalence relations that shows that the former is a full sub-Cartesian-closed category of the latter. We cannot pursue the categorical questions here, but note that there are many subcategories that might be of interest; for example, the equivalence relations with the intersection property are closed under $\to$, $\times$, and $+$.

Returning to the question of total functions we introduce this notation:

$$(7.9) \quad N = \{\langle n, n \rangle \mid n \in \omega\}.$$

This is the type of the integers *without* $\bot$ and $\top$, i.e., the total integers. We note that:

$$(7.10) \quad N = \{u \mid u = \langle u_0, u_0 \rangle,\, u_0 = \mathbf{int}(u_0),\, \mathbf{mid}(u_0) = 0\}.$$

Thus $N$ is a $\mathfrak{B}_\delta$-set. What is $N \to N$? We see:

$$(7.11) \quad f : N \to N \text{ iff } f : \mathbf{fun} \text{ and } f(n) \in \omega \text{ whenever } n \in \omega.$$

This $N \to N$ is indeed the type of all total functions from $\omega$ into $\omega$. It can be shown that $N \to N$ is also a $\mathfrak{B}_\delta$-set: good. But what is $(N \to N) \to N$? This is no longer a $\mathfrak{B}_\delta$-set, the best we can say is $\Pi_1^1$. By Theorem 7.1 it corresponds to the type of all
(extensional) *continuous* total functions from $N \to N$ into $N$. (The condition on $A$ and $B$ on the right side of (7.6) makes the concept of function embodied in $A \to B$ extensional, since the functions are meant to preserve the equivalence relations.)

A more precise discussion identifies $N \to N$ as a topological space, usually called the *Baire space*. If we introduce the finite discrete spaces by:

$$(7.12) \quad N_k = \{\langle n, n \rangle \mid n < k\},$$

then $N \to N_2$ can also be identified with a topological space, usually called the *Cantor space*. In this identification we find at the next type, say either $(N \to N) \to N$ or $(N \to N_2) \to N_2$, that elements correspond to the usual notion of continuous function defined in topological terms. However, these higher type spaces are not at all conveniently taken as *topological* spaces. Certain of them can be identified as *limit spaces* according to the work of Hyland, and for these $\to$, $\times$, and $+$ have the natural interpretation. We cannot enter into these details here, but we can remark that the higher type spaces become ever more complicated. Thus $((N \to N) \to N) \to N$ is a $\Pi_2^1$-set and each $\to$ will add another quantifier to the definition. This is reasonable, because to say that a function is total is to say that *all* its values are well-behaved. But if its domain is a complex space, this statement of totality is even more complex. Despite this complexity, however, it is possible to sort out what kind of mapping properties many functions have. We shall mention a few of the combinators.

**THEOREM 7.3 (The functionality theorem).** *The combinators $\mathbf{I}$, $\mathbf{K}$, and $\mathbf{S}$ enjoy the following functionality properties which hold for all equivalence relations $A$, $B$, $C$:*

(i) $\mathbf{I} : A \to A$;

(ii) $\mathbf{K} : A \to (B \to A)$;

(iii) $\mathbf{S} : (A \to (B \to C)) \to ((A \to B) \to (A \to C))$.

*Furthermore, these combinators are uniquely determined by these properties.*

Let us check that $S$ satisfies (iii). Suppose that:

$$f \, (A \to (B \to C)) \, f'.$$

We must show that:

$$\mathbf{S}(f) \, ((A \to B) \to (A \to C)) \, \mathbf{S}(f').$$

To this end suppose that:

$$g \, (A \to B) \, g'.$$

We must show that:

$$\mathbf{S}(f)(g) \, (A \to C) \, \mathbf{S}(f')(g').$$

To this end suppose that:

$$x \, A \, x'.$$

We must show that:

$$\mathbf{S}(f)(g)(x) \, C \, \mathbf{S}(f')(g')(x').$$

Now by definition of the combinator $\mathbf{S}$ we have:

$$\mathbf{S}(f)(g)(x) = f(x)(g(x)),$$

$$\mathbf{S}(f')(g')(x') = f'(x')(g'(x')).$$

By assumptions on $g$, $g'$ and on $x$, $x'$, we know:

$$g(x) \, B \, g'(x').$$

By assumptions on $f$, $f'$ and on $x$, $x'$, we know:

$$f(x) \, (B \to C) \, f'(x').$$

The desired conclusion now follows when we note such combinations as $\mathbf{S}(f)$ and $\mathbf{S}(f)(g)$ are indeed functions. (We are using Theorem 7.1(i) several times in this case.)

In the case of the converse, let us suppose by way of example that $k \in \mathbf{P}\omega$ is such that

$$k : A \to (B \to A)$$

holds for all equivalence relations $A$ and $B$. By specializing to, say, the identity relation we see that whatever $a \in \mathbf{P}\omega$ we take, both $k$ and $k(a)$ are functions. To establish that $k = \mathbf{K}$ we need to show that the equation:

$$k(a)(b) = a$$

holds for all $a, b \in \mathbf{P}\omega$. This is easy to prove, for we have only to set:

$$A = \{\langle a, a \rangle\} \quad \text{and} \quad B = \{\langle b, b \rangle\},$$

and the equation follows at once. Not all proofs are quite so easy, however.

In the case of the combinator $\mathbf{S}$ it is not strictly true to say that Theorem 7.3(iii) determines it outright. The exact formulation is this: if $s \in \mathbf{P}\omega$ is such that

$$s(f) = s(\lambda x \lambda y.\, f(x)(y)) \quad \text{and} \quad s(f)(g) = s(f)(\lambda x.\, g(x))$$

for all $f, g \in \mathbf{P}\omega$; and if

$$s : (A \to (B \to C)) \to ((A \to B) \to (A \to C))$$

for all $A$, $B$, $C$, then $s = \mathbf{S}$. In other words, we need to know that $s$ converts its first two arguments into functions with the right number of places before we can say that its explicit functionality identifies it as being the combinator $\mathbf{S}$.

In Hindley, Lercher and Seldin (1972) they show that the functionality property:

$$(7.13) \quad \lambda f \lambda g.\, f \circ g : (B \to C) \to ((A \to B) \to (A \to C)),$$

follows from Theorem 7.1(ii) and Theorem 7.3(ii) and (iii) in view of the identity:

$$(7.14) \quad \lambda f \lambda g.\, f \circ g = \mathbf{S}(\mathbf{K}(\mathbf{S}))(\mathbf{K})$$

(see Appendix A).

A more interesting result concerns the *iterators* defined as follows:

$$(7.15) \quad \mathbf{Z}_0 = \lambda f \lambda x.\, x,$$

$$(7.16) \quad \mathbf{Z}_{n+1} = \lambda f \lambda x.\, f(\mathbf{Z}_n(f)(x)),$$

In other words, $\mathbf{Z}_n(f)(x) = f^n(x)$. These natural combinators can be typed very easily, but Gordon Plotkin has shown that the obvious typing actually characterizes them.

**THEOREM 7.4 (The iterator theorem).** *The combinators* $\mathbf{Z}_n$ *enjoy the following functionality property which holds for all equivalence relations* $A$:

(i) $\mathbf{Z}_n : (A \to A) \to (A \to A)$.

*Further, if any element* $z \in \mathbf{P}\omega$ *satisfies (i) for all* $A$, *then it must be one of the iterators, provided that* $z(f) = z(\lambda x.\, f(x))$ *holds for all* $f \in \mathbf{P}\omega$.

That each of the $\mathbf{Z}_n$ satisfies Theorem 7.4(i) is obvious. Suppose $z$ were another such element. Then clearly:

$$z = \lambda f \lambda x.\, z(f)(x).$$

Suppose $f$ and $x$ are fixed for the moment. Let:

$$A = \{(f^n(x), f^n(x)) \mid n \in \omega\},$$

where we can suppose in addition that:

$$f = \lambda x.\, f(x).$$

Then $f : A \to A$ is clear, and so $z(f) : A \to A$ also. But $x : A$, therefore $z(f)(x) = f^n(x)$, for some $n \in \omega$, because $z(f)(x) : A$. The trouble with this easy part of the argument is that the integer $n$ depends on $f$ and $x$. What we must show is that it is independent of $f$ and $x$; then $z = \mathbf{Z}_n$ will follow.

Plotkin's method for this case is to introduce some independent successor functions:

$$(7.17) \quad \sigma_j = \lambda x.\, \{(j, k + 1) \mid (j, k) \in x\}.$$

Note that:

$$(7.18) \quad \sigma_j^m((j', 0)) = \begin{cases} (j, m) & \text{if } j = j'; \\ \bot & \text{if } j \neq j'. \end{cases}$$

It then follows that:

$$(7.19) \quad (\sigma_j \cup \sigma_{j'})^m((j, 0) \cup (j', 0)) = (j, m) \cup (j', m).$$

Having these identities, we return to the argument. From what we saw before, given $j \in \omega$, there is an $n_j$ such that:

$$z(\sigma_j)((j, 0)) = \sigma_j^{n_j}((j, 0)) = (j, n_j)$$

Take any two $j, j' \in \omega$. We also know there is an $n \in \omega$ where:

$$z(\sigma_j \cup \sigma_{j'})((j, 0) \cup (j', 0)) = (j, n) \cup (j', n).$$
in view of (7.19). But since $\sigma_j \subseteq \sigma_j \cup \sigma_{j'}$ and $\sigma_{j'} \subseteq \sigma_j \cup \sigma_{j'}$, we have:

$$(j, n_j) \cup (j', n_{j'}) \subseteq (j, n) \cup (j', n).$$

It follows that

$$n_j = n = n_{j'},$$

and so they are all equal. This determines the fixed $n \in \omega$ we want.

Suppose that both $f$ and $x$ are finite sets in $\mathbf{P}\omega$. Choose $j > \max(f \cup x)$. Let $A$ this time be the least equivalence relation such that:

$$f^m(x) \, A \, f^m(x) \cup (j, m)$$

holds for all $m \in \omega$. We then check that:

$$\lambda x.\, f(x) \, (A \to A) \, (\lambda x.\, f(x)) \cup \sigma_j.$$

Therefore, we have:

$$z(\lambda x.\, f(x)) \, (A \to A) \, z((\lambda x.\, f(x)) \cup \sigma_j),$$

and since $x \, A \, x \cup (j, 0)$, we get:

$$z(\lambda x.\, f(x))(x) \, A \, z((\lambda x.\, f(x)) \cup \sigma_j)(x \cup (j, 0)).$$

Now there is an integer $m \in \omega$ such that:

$$
\begin{aligned}
z((\lambda x.\, f(x)) \cup \sigma_j)(x \cup (j, 0)) &= f^m(x) \cup \sigma_j^m((j, 0)) \\
&= f^m(x) \cup (j, m),
\end{aligned}
$$

where we have been able to separate $f$ and $\sigma$ because $j$ is so large. But the right-hand side must contain $z(\sigma_j)(j, 0) = (j, n)$. Thus $m$ and our fixed $n$ are the same. The other element

$$z(\lambda x.\, f(x))(x) = f^q(x)$$

for some $q \in \omega$. Thus we have:

$$f^q(x) \, A \, f^n(x) \cup (j, n).$$

Again since $j$ is so large, $(j, n) \notin f^q(x)$. Thus by our choice of $A$ we must have $f^q(x) = f^n(x)$. This means then, since $n$ is fixed, that for *all finite* $f, x$:

$$z(\lambda x.\, f(x))(x) = f^n(x).$$

But then by continuity this equation holds for *all* $f, x$. It follows now that $z = \mathbf{Z}_n$, by the proviso of the theorem.

These results bring up many questions which we leave unanswered here. For example, which combinators (i.e., pure $\lambda$-terms) have functionality as in the examples above, and can we decide when a term is one such? In particular, can the diagonal combinator $\lambda x.\, x(x)$ be typed? (The argument of Hindley, et al. (1972, p. 81) is purely formal and does not apparently apply to the model.) What about terms in LAMBDA beyond the pure $\lambda$-calculus?
