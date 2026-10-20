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

**Lean 4**

- [DataTypesAsLattices/Functionality.lean](DomainTheory/DataTypesAsLattices/Functionality.lean)
- [DataTypesAsLattices/Functionality/Basic.lean](DomainTheory/DataTypesAsLattices/Functionality/Basic.lean)
- [DataTypesAsLattices/Functionality/Ea.lean](DomainTheory/DataTypesAsLattices/Functionality/Ea.lean)
- [DataTypesAsLattices/Functionality/HF.lean](DomainTheory/DataTypesAsLattices/Functionality/HF.lean)
- [DataTypesAsLattices/Functionality/HF_app.lean](DomainTheory/DataTypesAsLattices/Functionality/HF_app.lean)
- [DataTypesAsLattices/Functionality/HF_app2.lean](DomainTheory/DataTypesAsLattices/Functionality/HF_app2.lean)
- [DataTypesAsLattices/Functionality/HF_inner_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/HF_inner_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/HF_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/HF_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/Hcomb.lean](DomainTheory/DataTypesAsLattices/Functionality/Hcomb.lean)
- [DataTypesAsLattices/Functionality/Hcomb_app.lean](DomainTheory/DataTypesAsLattices/Functionality/Hcomb_app.lean)
- [DataTypesAsLattices/Functionality/Hcomb_decode.lean](DomainTheory/DataTypesAsLattices/Functionality/Hcomb_decode.lean)
- [DataTypesAsLattices/Functionality/Hcomb_typed.lean](DomainTheory/DataTypesAsLattices/Functionality/Hcomb_typed.lean)
- [DataTypesAsLattices/Functionality/Hfun.lean](DomainTheory/DataTypesAsLattices/Functionality/Hfun.lean)
- [DataTypesAsLattices/Functionality/Hfun_app2.lean](DomainTheory/DataTypesAsLattices/Functionality/Hfun_app2.lean)
- [DataTypesAsLattices/Functionality/Hfun_decode.lean](DomainTheory/DataTypesAsLattices/Functionality/Hfun_decode.lean)
- [DataTypesAsLattices/Functionality/Hfun_fixed.lean](DomainTheory/DataTypesAsLattices/Functionality/Hfun_fixed.lean)
- [DataTypesAsLattices/Functionality/Hfun_interp.lean](DomainTheory/DataTypesAsLattices/Functionality/Hfun_interp.lean)
- [DataTypesAsLattices/Functionality/Hinterp.lean](DomainTheory/DataTypesAsLattices/Functionality/Hinterp.lean)
- [DataTypesAsLattices/Functionality/Hinterp_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/Hinterp_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/Hstep.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep.lean)
- [DataTypesAsLattices/Functionality/Hstep_isScottContinuous_H.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep_isScottContinuous_H.lean)
- [DataTypesAsLattices/Functionality/Hstep_isScottContinuous_e.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep_isScottContinuous_e.lean)
- [DataTypesAsLattices/Functionality/Hstep_isScottContinuous_t.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep_isScottContinuous_t.lean)
- [DataTypesAsLattices/Functionality/Hstep_tag0.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep_tag0.lean)
- [DataTypesAsLattices/Functionality/Hstep_tag1.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep_tag1.lean)
- [DataTypesAsLattices/Functionality/Hstep_tag2.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep_tag2.lean)
- [DataTypesAsLattices/Functionality/Hstep_tag3.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep_tag3.lean)
- [DataTypesAsLattices/Functionality/Hstep_tag4.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep_tag4.lean)
- [DataTypesAsLattices/Functionality/Hstep_tag5.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep_tag5.lean)
- [DataTypesAsLattices/Functionality/Hstep_tag6.lean](DomainTheory/DataTypesAsLattices/Functionality/Hstep_tag6.lean)
- [DataTypesAsLattices/Functionality/Htyped.lean](DomainTheory/DataTypesAsLattices/Functionality/Htyped.lean)
- [DataTypesAsLattices/Functionality/Htyped_app.lean](DomainTheory/DataTypesAsLattices/Functionality/Htyped_app.lean)
- [DataTypesAsLattices/Functionality/Htyped_typed.lean](DomainTheory/DataTypesAsLattices/Functionality/Htyped_typed.lean)
- [DataTypesAsLattices/Functionality/Icomb_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Icomb_isGraph.lean)
- [DataTypesAsLattices/Functionality/Kcomb_app.lean](DomainTheory/DataTypesAsLattices/Functionality/Kcomb_app.lean)
- [DataTypesAsLattices/Functionality/Kcomb_app2.lean](DomainTheory/DataTypesAsLattices/Functionality/Kcomb_app2.lean)
- [DataTypesAsLattices/Functionality/Kcomb_app_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Kcomb_app_isGraph.lean)
- [DataTypesAsLattices/Functionality/Kcomb_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Kcomb_isGraph.lean)
- [DataTypesAsLattices/Functionality/LambTerm.lean](DomainTheory/DataTypesAsLattices/Functionality/LambTerm.lean)
- [DataTypesAsLattices/Functionality/Nk.lean](DomainTheory/DataTypesAsLattices/Functionality/Nk.lean)
- [DataTypesAsLattices/Functionality/Nrel.lean](DomainTheory/DataTypesAsLattices/Functionality/Nrel.lean)
- [DataTypesAsLattices/Functionality/RestrictedEquiv.lean](DomainTheory/DataTypesAsLattices/Functionality/RestrictedEquiv.lean)
- [DataTypesAsLattices/Functionality/Scomb_app.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_app.lean)
- [DataTypesAsLattices/Functionality/Scomb_app2.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_app2.lean)
- [DataTypesAsLattices/Functionality/Scomb_app2_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_app2_isGraph.lean)
- [DataTypesAsLattices/Functionality/Scomb_app3.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_app3.lean)
- [DataTypesAsLattices/Functionality/Scomb_app_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_app_isGraph.lean)
- [DataTypesAsLattices/Functionality/Scomb_inner_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_inner_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/Scomb_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_isGraph.lean)
- [DataTypesAsLattices/Functionality/Scomb_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_map_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/Scomb_mid_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/Scomb_mid_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/Z.lean](DomainTheory/DataTypesAsLattices/Functionality/Z.lean)
- [DataTypesAsLattices/Functionality/Z_finite_bound.lean](DomainTheory/DataTypesAsLattices/Functionality/Z_finite_bound.lean)
- [DataTypesAsLattices/Functionality/Z_finite_no_tag.lean](DomainTheory/DataTypesAsLattices/Functionality/Z_finite_no_tag.lean)
- [DataTypesAsLattices/Functionality/Z_graph_funOf.lean](DomainTheory/DataTypesAsLattices/Functionality/Z_graph_funOf.lean)
- [DataTypesAsLattices/Functionality/Z_isScottContinuous_left.lean](DomainTheory/DataTypesAsLattices/Functionality/Z_isScottContinuous_left.lean)
- [DataTypesAsLattices/Functionality/Z_isScottContinuous_right.lean](DomainTheory/DataTypesAsLattices/Functionality/Z_isScottContinuous_right.lean)
- [DataTypesAsLattices/Functionality/Z_rel.lean](DomainTheory/DataTypesAsLattices/Functionality/Z_rel.lean)
- [DataTypesAsLattices/Functionality/Zcomb.lean](DomainTheory/DataTypesAsLattices/Functionality/Zcomb.lean)
- [DataTypesAsLattices/Functionality/Zcomb_app.lean](DomainTheory/DataTypesAsLattices/Functionality/Zcomb_app.lean)
- [DataTypesAsLattices/Functionality/Zcomb_app2.lean](DomainTheory/DataTypesAsLattices/Functionality/Zcomb_app2.lean)
- [DataTypesAsLattices/Functionality/Zcomb_app_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Zcomb_app_isGraph.lean)
- [DataTypesAsLattices/Functionality/Zcomb_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/Zcomb_isGraph.lean)
- [DataTypesAsLattices/Functionality/Zcomb_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/Zcomb_map_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/arrowE.lean](DomainTheory/DataTypesAsLattices/Functionality/arrowE.lean)
- [DataTypesAsLattices/Functionality/arrowR_diag_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/arrowR_diag_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/comp_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/comp_isGraph.lean)
- [DataTypesAsLattices/Functionality/condSet_bot.lean](DomainTheory/DataTypesAsLattices/Functionality/condSet_bot.lean)
- [DataTypesAsLattices/Functionality/condSet_ofNat_one.lean](DomainTheory/DataTypesAsLattices/Functionality/condSet_ofNat_one.lean)
- [DataTypesAsLattices/Functionality/condSet_ofNat_succ.lean](DomainTheory/DataTypesAsLattices/Functionality/condSet_ofNat_succ.lean)
- [DataTypesAsLattices/Functionality/condSet_ofNat_zero.lean](DomainTheory/DataTypesAsLattices/Functionality/condSet_ofNat_zero.lean)
- [DataTypesAsLattices/Functionality/condSet_same_bot.lean](DomainTheory/DataTypesAsLattices/Functionality/condSet_same_bot.lean)
- [DataTypesAsLattices/Functionality/condSet_same_of_mem.lean](DomainTheory/DataTypesAsLattices/Functionality/condSet_same_of_mem.lean)
- [DataTypesAsLattices/Functionality/continuous_nary.lean](DomainTheory/DataTypesAsLattices/Functionality/continuous_nary.lean)
- [DataTypesAsLattices/Functionality/continuous_on_diag.lean](DomainTheory/DataTypesAsLattices/Functionality/continuous_on_diag.lean)
- [DataTypesAsLattices/Functionality/continuous_tuple.lean](DomainTheory/DataTypesAsLattices/Functionality/continuous_tuple.lean)
- [DataTypesAsLattices/Functionality/curryC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/curryC_app.lean)
- [DataTypesAsLattices/Functionality/curryC_app2.lean](DomainTheory/DataTypesAsLattices/Functionality/curryC_app2.lean)
- [DataTypesAsLattices/Functionality/curryC_app3.lean](DomainTheory/DataTypesAsLattices/Functionality/curryC_app3.lean)
- [DataTypesAsLattices/Functionality/curryC_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/curryC_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/curry_body_isScottContinuous_y.lean](DomainTheory/DataTypesAsLattices/Functionality/curry_body_isScottContinuous_y.lean)
- [DataTypesAsLattices/Functionality/curry_mid_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/curry_mid_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/diagC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/diagC_app.lean)
- [DataTypesAsLattices/Functionality/emptyE.lean](DomainTheory/DataTypesAsLattices/Functionality/emptyE.lean)
- [DataTypesAsLattices/Functionality/encodeExp.lean](DomainTheory/DataTypesAsLattices/Functionality/encodeExp.lean)
- [DataTypesAsLattices/Functionality/encodeExp_typed.lean](DomainTheory/DataTypesAsLattices/Functionality/encodeExp_typed.lean)
- [DataTypesAsLattices/Functionality/envR_app.lean](DomainTheory/DataTypesAsLattices/Functionality/envR_app.lean)
- [DataTypesAsLattices/Functionality/envR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/envR_isRetract.lean)
- [DataTypesAsLattices/Functionality/envR_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/envR_map_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/eq_4_12.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_12.lean)
- [DataTypesAsLattices/Functionality/eq_4_13.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_13.lean)
- [DataTypesAsLattices/Functionality/eq_4_17.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_17.lean)
- [DataTypesAsLattices/Functionality/eq_4_18.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_18.lean)
- [DataTypesAsLattices/Functionality/eq_4_19.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_19.lean)
- [DataTypesAsLattices/Functionality/eq_4_20.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_20.lean)
- [DataTypesAsLattices/Functionality/eq_4_21.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_21.lean)
- [DataTypesAsLattices/Functionality/eq_4_24.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_24.lean)
- [DataTypesAsLattices/Functionality/eq_4_25.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_25.lean)
- [DataTypesAsLattices/Functionality/eq_4_32.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_32.lean)
- [DataTypesAsLattices/Functionality/eq_4_33.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_33.lean)
- [DataTypesAsLattices/Functionality/eq_4_34.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_34.lean)
- [DataTypesAsLattices/Functionality/eq_4_35.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_35.lean)
- [DataTypesAsLattices/Functionality/eq_4_36.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_36.lean)
- [DataTypesAsLattices/Functionality/eq_4_37.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_37.lean)
- [DataTypesAsLattices/Functionality/eq_4_38.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_38.lean)
- [DataTypesAsLattices/Functionality/eq_4_39.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_39.lean)
- [DataTypesAsLattices/Functionality/eq_4_44.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_44.lean)
- [DataTypesAsLattices/Functionality/eq_4_45.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_4_45.lean)
- [DataTypesAsLattices/Functionality/eq_7_18_eq.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_7_18_eq.lean)
- [DataTypesAsLattices/Functionality/eq_7_18_ne.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_7_18_ne.lean)
- [DataTypesAsLattices/Functionality/eq_7_19.lean](DomainTheory/DataTypesAsLattices/Functionality/eq_7_19.lean)
- [DataTypesAsLattices/Functionality/eraseTag.lean](DomainTheory/DataTypesAsLattices/Functionality/eraseTag.lean)
- [DataTypesAsLattices/Functionality/eraseTag_Z_finite.lean](DomainTheory/DataTypesAsLattices/Functionality/eraseTag_Z_finite.lean)
- [DataTypesAsLattices/Functionality/eraseTag_Z_finite_union.lean](DomainTheory/DataTypesAsLattices/Functionality/eraseTag_Z_finite_union.lean)
- [DataTypesAsLattices/Functionality/eta2_app.lean](DomainTheory/DataTypesAsLattices/Functionality/eta2_app.lean)
- [DataTypesAsLattices/Functionality/eta2_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/eta2_map_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/evalC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/evalC_app.lean)
- [DataTypesAsLattices/Functionality/evalC_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/evalC_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/eval_curry.lean](DomainTheory/DataTypesAsLattices/Functionality/eval_curry.lean)
- [DataTypesAsLattices/Functionality/expF_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/expF_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/expPayload.lean](DomainTheory/DataTypesAsLattices/Functionality/expPayload.lean)
- [DataTypesAsLattices/Functionality/expR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/expR_isRetract.lean)
- [DataTypesAsLattices/Functionality/expTag.lean](DomainTheory/DataTypesAsLattices/Functionality/expTag.lean)
- [DataTypesAsLattices/Functionality/finite_sigma_plain_app.lean](DomainTheory/DataTypesAsLattices/Functionality/finite_sigma_plain_app.lean)
- [DataTypesAsLattices/Functionality/finite_sigma_union_app.lean](DomainTheory/DataTypesAsLattices/Functionality/finite_sigma_union_app.lean)
- [DataTypesAsLattices/Functionality/funOf_condSet.lean](DomainTheory/DataTypesAsLattices/Functionality/funOf_condSet.lean)
- [DataTypesAsLattices/Functionality/funOf_dcondSet.lean](DomainTheory/DataTypesAsLattices/Functionality/funOf_dcondSet.lean)
- [DataTypesAsLattices/Functionality/funOf_e_union_fresh.lean](DomainTheory/DataTypesAsLattices/Functionality/funOf_e_union_fresh.lean)
- [DataTypesAsLattices/Functionality/funOf_top.lean](DomainTheory/DataTypesAsLattices/Functionality/funOf_top.lean)
- [DataTypesAsLattices/Functionality/graph_funOf_ext.lean](DomainTheory/DataTypesAsLattices/Functionality/graph_funOf_ext.lean)
- [DataTypesAsLattices/Functionality/hApp.lean](DomainTheory/DataTypesAsLattices/Functionality/hApp.lean)
- [DataTypesAsLattices/Functionality/hApp_isScottContinuous_H.lean](DomainTheory/DataTypesAsLattices/Functionality/hApp_isScottContinuous_H.lean)
- [DataTypesAsLattices/Functionality/hApp_isScottContinuous_e.lean](DomainTheory/DataTypesAsLattices/Functionality/hApp_isScottContinuous_e.lean)
- [DataTypesAsLattices/Functionality/hApp_isScottContinuous_t.lean](DomainTheory/DataTypesAsLattices/Functionality/hApp_isScottContinuous_t.lean)
- [DataTypesAsLattices/Functionality/hApply.lean](DomainTheory/DataTypesAsLattices/Functionality/hApply.lean)
- [DataTypesAsLattices/Functionality/hApply_isScottContinuous_H.lean](DomainTheory/DataTypesAsLattices/Functionality/hApply_isScottContinuous_H.lean)
- [DataTypesAsLattices/Functionality/hApply_isScottContinuous_e.lean](DomainTheory/DataTypesAsLattices/Functionality/hApply_isScottContinuous_e.lean)
- [DataTypesAsLattices/Functionality/hApply_payload_isScottContinuous_e.lean](DomainTheory/DataTypesAsLattices/Functionality/hApply_payload_isScottContinuous_e.lean)
- [DataTypesAsLattices/Functionality/hCond.lean](DomainTheory/DataTypesAsLattices/Functionality/hCond.lean)
- [DataTypesAsLattices/Functionality/hCond_isScottContinuous_H.lean](DomainTheory/DataTypesAsLattices/Functionality/hCond_isScottContinuous_H.lean)
- [DataTypesAsLattices/Functionality/hCond_isScottContinuous_e.lean](DomainTheory/DataTypesAsLattices/Functionality/hCond_isScottContinuous_e.lean)
- [DataTypesAsLattices/Functionality/hCond_isScottContinuous_t.lean](DomainTheory/DataTypesAsLattices/Functionality/hCond_isScottContinuous_t.lean)
- [DataTypesAsLattices/Functionality/hLam.lean](DomainTheory/DataTypesAsLattices/Functionality/hLam.lean)
- [DataTypesAsLattices/Functionality/hLam_isScottContinuous_H.lean](DomainTheory/DataTypesAsLattices/Functionality/hLam_isScottContinuous_H.lean)
- [DataTypesAsLattices/Functionality/hLam_isScottContinuous_e.lean](DomainTheory/DataTypesAsLattices/Functionality/hLam_isScottContinuous_e.lean)
- [DataTypesAsLattices/Functionality/hLam_isScottContinuous_t.lean](DomainTheory/DataTypesAsLattices/Functionality/hLam_isScottContinuous_t.lean)
- [DataTypesAsLattices/Functionality/hPred.lean](DomainTheory/DataTypesAsLattices/Functionality/hPred.lean)
- [DataTypesAsLattices/Functionality/hPred_isScottContinuous_H.lean](DomainTheory/DataTypesAsLattices/Functionality/hPred_isScottContinuous_H.lean)
- [DataTypesAsLattices/Functionality/hPred_isScottContinuous_e.lean](DomainTheory/DataTypesAsLattices/Functionality/hPred_isScottContinuous_e.lean)
- [DataTypesAsLattices/Functionality/hPred_isScottContinuous_t.lean](DomainTheory/DataTypesAsLattices/Functionality/hPred_isScottContinuous_t.lean)
- [DataTypesAsLattices/Functionality/hSucc.lean](DomainTheory/DataTypesAsLattices/Functionality/hSucc.lean)
- [DataTypesAsLattices/Functionality/hSucc_isScottContinuous_H.lean](DomainTheory/DataTypesAsLattices/Functionality/hSucc_isScottContinuous_H.lean)
- [DataTypesAsLattices/Functionality/hSucc_isScottContinuous_e.lean](DomainTheory/DataTypesAsLattices/Functionality/hSucc_isScottContinuous_e.lean)
- [DataTypesAsLattices/Functionality/hSucc_isScottContinuous_t.lean](DomainTheory/DataTypesAsLattices/Functionality/hSucc_isScottContinuous_t.lean)
- [DataTypesAsLattices/Functionality/hVar.lean](DomainTheory/DataTypesAsLattices/Functionality/hVar.lean)
- [DataTypesAsLattices/Functionality/hVar_isScottContinuous_e.lean](DomainTheory/DataTypesAsLattices/Functionality/hVar_isScottContinuous_e.lean)
- [DataTypesAsLattices/Functionality/hVar_isScottContinuous_t.lean](DomainTheory/DataTypesAsLattices/Functionality/hVar_isScottContinuous_t.lean)
- [DataTypesAsLattices/Functionality/hZero.lean](DomainTheory/DataTypesAsLattices/Functionality/hZero.lean)
- [DataTypesAsLattices/Functionality/inleftC.lean](DomainTheory/DataTypesAsLattices/Functionality/inleftC.lean)
- [DataTypesAsLattices/Functionality/inleftC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/inleftC_app.lean)
- [DataTypesAsLattices/Functionality/inrightC.lean](DomainTheory/DataTypesAsLattices/Functionality/inrightC.lean)
- [DataTypesAsLattices/Functionality/inrightC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/inrightC_app.lean)
- [DataTypesAsLattices/Functionality/iterateE.lean](DomainTheory/DataTypesAsLattices/Functionality/iterateE.lean)
- [DataTypesAsLattices/Functionality/kerE.lean](DomainTheory/DataTypesAsLattices/Functionality/kerE.lean)
- [DataTypesAsLattices/Functionality/kerE_repr.lean](DomainTheory/DataTypesAsLattices/Functionality/kerE_repr.lean)
- [DataTypesAsLattices/Functionality/lambF_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/lambF_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/lambR_fixedPoint.lean](DomainTheory/DataTypesAsLattices/Functionality/lambR_fixedPoint.lean)
- [DataTypesAsLattices/Functionality/lambR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/lambR_isRetract.lean)
- [DataTypesAsLattices/Functionality/mem.lean](DomainTheory/DataTypesAsLattices/Functionality/mem.lean)
- [DataTypesAsLattices/Functionality/normalized_finite_app.lean](DomainTheory/DataTypesAsLattices/Functionality/normalized_finite_app.lean)
- [DataTypesAsLattices/Functionality/normalized_finite_fresh_app.lean](DomainTheory/DataTypesAsLattices/Functionality/normalized_finite_fresh_app.lean)
- [DataTypesAsLattices/Functionality/outC.lean](DomainTheory/DataTypesAsLattices/Functionality/outC.lean)
- [DataTypesAsLattices/Functionality/outC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/outC_app.lean)
- [DataTypesAsLattices/Functionality/outleftC.lean](DomainTheory/DataTypesAsLattices/Functionality/outleftC.lean)
- [DataTypesAsLattices/Functionality/outleftC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/outleftC_app.lean)
- [DataTypesAsLattices/Functionality/outleftC_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/outleftC_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/outrightC.lean](DomainTheory/DataTypesAsLattices/Functionality/outrightC.lean)
- [DataTypesAsLattices/Functionality/outrightC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/outrightC_app.lean)
- [DataTypesAsLattices/Functionality/outrightC_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/outrightC_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/pairElem.lean](DomainTheory/DataTypesAsLattices/Functionality/pairElem.lean)
- [DataTypesAsLattices/Functionality/pairElem_eq_pairSeq.lean](DomainTheory/DataTypesAsLattices/Functionality/pairElem_eq_pairSeq.lean)
- [DataTypesAsLattices/Functionality/pairElem_fst.lean](DomainTheory/DataTypesAsLattices/Functionality/pairElem_fst.lean)
- [DataTypesAsLattices/Functionality/pairElem_inj.lean](DomainTheory/DataTypesAsLattices/Functionality/pairElem_inj.lean)
- [DataTypesAsLattices/Functionality/pairElem_snd.lean](DomainTheory/DataTypesAsLattices/Functionality/pairElem_snd.lean)
- [DataTypesAsLattices/Functionality/pairElem_tag_ne.lean](DomainTheory/DataTypesAsLattices/Functionality/pairElem_tag_ne.lean)
- [DataTypesAsLattices/Functionality/pairMed.lean](DomainTheory/DataTypesAsLattices/Functionality/pairMed.lean)
- [DataTypesAsLattices/Functionality/pairSeq_app_one.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_app_one.lean)
- [DataTypesAsLattices/Functionality/pairSeq_app_zero.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_app_zero.lean)
- [DataTypesAsLattices/Functionality/pairSeq_bot.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_bot.lean)
- [DataTypesAsLattices/Functionality/pairSeq_inj.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_inj.lean)
- [DataTypesAsLattices/Functionality/pairSeq_isScottContinuous_left.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_isScottContinuous_left.lean)
- [DataTypesAsLattices/Functionality/pairSeq_isScottContinuous_right.lean](DomainTheory/DataTypesAsLattices/Functionality/pairSeq_isScottContinuous_right.lean)
- [DataTypesAsLattices/Functionality/plotkinE.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkinE.lean)
- [DataTypesAsLattices/Functionality/plotkinE_erase.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkinE_erase.lean)
- [DataTypesAsLattices/Functionality/plotkinGood.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkinGood.lean)
- [DataTypesAsLattices/Functionality/plotkinRel.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkinRel.lean)
- [DataTypesAsLattices/Functionality/plotkin_finite_separation.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkin_finite_separation.lean)
- [DataTypesAsLattices/Functionality/plotkin_function_related.lean](DomainTheory/DataTypesAsLattices/Functionality/plotkin_function_related.lean)
- [DataTypesAsLattices/Functionality/plus7_app.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app.lean)
- [DataTypesAsLattices/Functionality/plus7_app_bot.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app_bot.lean)
- [DataTypesAsLattices/Functionality/plus7_app_tag0.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app_tag0.lean)
- [DataTypesAsLattices/Functionality/plus7_app_tag1.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app_tag1.lean)
- [DataTypesAsLattices/Functionality/plus7_app_tag2.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app_tag2.lean)
- [DataTypesAsLattices/Functionality/plus7_app_tag3.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app_tag3.lean)
- [DataTypesAsLattices/Functionality/plus7_app_tag4.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app_tag4.lean)
- [DataTypesAsLattices/Functionality/plus7_app_tag5.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app_tag5.lean)
- [DataTypesAsLattices/Functionality/plus7_app_tag6.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app_tag6.lean)
- [DataTypesAsLattices/Functionality/plus7_app_top.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_app_top.lean)
- [DataTypesAsLattices/Functionality/plus7_comp_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_comp_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/plus7_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_isRetract.lean)
- [DataTypesAsLattices/Functionality/plus7_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_map_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/plus7_typed_inl0.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl0.lean)
- [DataTypesAsLattices/Functionality/plus7_typed_inl1.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl1.lean)
- [DataTypesAsLattices/Functionality/plus7_typed_inl2.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl2.lean)
- [DataTypesAsLattices/Functionality/plus7_typed_inl3.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl3.lean)
- [DataTypesAsLattices/Functionality/plus7_typed_inl4.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl4.lean)
- [DataTypesAsLattices/Functionality/plus7_typed_inl5.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl5.lean)
- [DataTypesAsLattices/Functionality/plus7_typed_inl6.lean](DomainTheory/DataTypesAsLattices/Functionality/plus7_typed_inl6.lean)
- [DataTypesAsLattices/Functionality/plusR_app.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_app.lean)
- [DataTypesAsLattices/Functionality/plusR_app_bot.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_app_bot.lean)
- [DataTypesAsLattices/Functionality/plusR_app_top.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_app_top.lean)
- [DataTypesAsLattices/Functionality/plusR_fst.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_fst.lean)
- [DataTypesAsLattices/Functionality/plusR_functor.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_functor.lean)
- [DataTypesAsLattices/Functionality/plusR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_isRetract.lean)
- [DataTypesAsLattices/Functionality/plusR_isStrict.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_isStrict.lean)
- [DataTypesAsLattices/Functionality/plusR_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_map_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/plusR_retractLe.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_retractLe.lean)
- [DataTypesAsLattices/Functionality/plusR_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_right_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/plusR_snd.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_snd.lean)
- [DataTypesAsLattices/Functionality/plusR_typed_bot.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_typed_bot.lean)
- [DataTypesAsLattices/Functionality/plusR_typed_iff.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_typed_iff.lean)
- [DataTypesAsLattices/Functionality/plusR_typed_inl.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_typed_inl.lean)
- [DataTypesAsLattices/Functionality/plusR_typed_inr.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_typed_inr.lean)
- [DataTypesAsLattices/Functionality/plusR_typed_top.lean](DomainTheory/DataTypesAsLattices/Functionality/plusR_typed_top.lean)
- [DataTypesAsLattices/Functionality/predSet_iterate_expTag_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/predSet_iterate_expTag_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/predSet_iterate_ofNat.lean](DomainTheory/DataTypesAsLattices/Functionality/predSet_iterate_ofNat.lean)
- [DataTypesAsLattices/Functionality/predSet_iterate_self.lean](DomainTheory/DataTypesAsLattices/Functionality/predSet_iterate_self.lean)
- [DataTypesAsLattices/Functionality/prodE.lean](DomainTheory/DataTypesAsLattices/Functionality/prodE.lean)
- [DataTypesAsLattices/Functionality/seq4_app.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_app.lean)
- [DataTypesAsLattices/Functionality/seq4_app_one.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_app_one.lean)
- [DataTypesAsLattices/Functionality/seq4_app_three.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_app_three.lean)
- [DataTypesAsLattices/Functionality/seq4_app_two.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_app_two.lean)
- [DataTypesAsLattices/Functionality/seq4_app_zero.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_app_zero.lean)
- [DataTypesAsLattices/Functionality/seq4_body_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_body_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/seq4_comp_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_comp_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/seq4_isScottContinuous_each.lean](DomainTheory/DataTypesAsLattices/Functionality/seq4_isScottContinuous_each.lean)
- [DataTypesAsLattices/Functionality/sigmaJ.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ.lean)
- [DataTypesAsLattices/Functionality/sigmaJ_app.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ_app.lean)
- [DataTypesAsLattices/Functionality/sigmaJ_bot.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ_bot.lean)
- [DataTypesAsLattices/Functionality/sigmaJ_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/sigmaJ_of_no_tag.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ_of_no_tag.lean)
- [DataTypesAsLattices/Functionality/sigmaJ_pair_union.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ_pair_union.lean)
- [DataTypesAsLattices/Functionality/sigmaJ_succ_ne.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ_succ_ne.lean)
- [DataTypesAsLattices/Functionality/sigmaJ_succ_singleton.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ_succ_singleton.lean)
- [DataTypesAsLattices/Functionality/sigmaJ_union_fresh.lean](DomainTheory/DataTypesAsLattices/Functionality/sigmaJ_union_fresh.lean)
- [DataTypesAsLattices/Functionality/singletonE.lean](DomainTheory/DataTypesAsLattices/Functionality/singletonE.lean)
- [DataTypesAsLattices/Functionality/singletonE_mem.lean](DomainTheory/DataTypesAsLattices/Functionality/singletonE_mem.lean)
- [DataTypesAsLattices/Functionality/sumE.lean](DomainTheory/DataTypesAsLattices/Functionality/sumE.lean)
- [DataTypesAsLattices/Functionality/sumMed.lean](DomainTheory/DataTypesAsLattices/Functionality/sumMed.lean)
- [DataTypesAsLattices/Functionality/sumMed_app.lean](DomainTheory/DataTypesAsLattices/Functionality/sumMed_app.lean)
- [DataTypesAsLattices/Functionality/sumMed_app_inl.lean](DomainTheory/DataTypesAsLattices/Functionality/sumMed_app_inl.lean)
- [DataTypesAsLattices/Functionality/sumMed_app_inr.lean](DomainTheory/DataTypesAsLattices/Functionality/sumMed_app_inr.lean)
- [DataTypesAsLattices/Functionality/sumMed_body_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/sumMed_body_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/sumMed_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/sumMed_isGraph.lean)
- [DataTypesAsLattices/Functionality/sumMed_rel.lean](DomainTheory/DataTypesAsLattices/Functionality/sumMed_rel.lean)
- [DataTypesAsLattices/Functionality/sumMed_rel_unique.lean](DomainTheory/DataTypesAsLattices/Functionality/sumMed_rel_unique.lean)
- [DataTypesAsLattices/Functionality/tagInj_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tagInj_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/tagInj_one.lean](DomainTheory/DataTypesAsLattices/Functionality/tagInj_one.lean)
- [DataTypesAsLattices/Functionality/tagInj_zero.lean](DomainTheory/DataTypesAsLattices/Functionality/tagInj_zero.lean)
- [DataTypesAsLattices/Functionality/tensor4_app.lean](DomainTheory/DataTypesAsLattices/Functionality/tensor4_app.lean)
- [DataTypesAsLattices/Functionality/tensor4_diag_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tensor4_diag_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/tensor4_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/tensor4_isRetract.lean)
- [DataTypesAsLattices/Functionality/tensor4_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tensor4_map_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/tensorR_app.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_app.lean)
- [DataTypesAsLattices/Functionality/tensorR_diag_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_diag_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/tensorR_functor.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_functor.lean)
- [DataTypesAsLattices/Functionality/tensorR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_isRetract.lean)
- [DataTypesAsLattices/Functionality/tensorR_isStrict.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_isStrict.lean)
- [DataTypesAsLattices/Functionality/tensorR_map_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_map_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/tensorR_retractLe.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_retractLe.lean)
- [DataTypesAsLattices/Functionality/tensorR_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/tensorR_right_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/theorem_4_4_med.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_4_4_med.lean)
- [DataTypesAsLattices/Functionality/theorem_4_4_med_unique.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_4_4_med_unique.lean)
- [DataTypesAsLattices/Functionality/theorem_4_4_typed.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_4_4_typed.lean)
- [DataTypesAsLattices/Functionality/theorem_4_5_sum.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_4_5_sum.lean)
- [DataTypesAsLattices/Functionality/theorem_7_1.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_1.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_2.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_i.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_2_i.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_i_iso.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_2_i_iso.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_ii.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_2_ii.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_ii_of_typed.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_2_ii_of_typed.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_iii.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_2_iii.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_iii_exact.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_2_iii_exact.lean)
- [DataTypesAsLattices/Functionality/theorem_7_2_iv.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_2_iv.lean)
- [DataTypesAsLattices/Functionality/theorem_7_3.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_3.lean)
- [DataTypesAsLattices/Functionality/theorem_7_3_I_unique.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_3_I_unique.lean)
- [DataTypesAsLattices/Functionality/theorem_7_3_K_unique.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_3_K_unique.lean)
- [DataTypesAsLattices/Functionality/theorem_7_3_S_unique.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_3_S_unique.lean)
- [DataTypesAsLattices/Functionality/theorem_7_3_i.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_3_i.lean)
- [DataTypesAsLattices/Functionality/theorem_7_3_ii.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_3_ii.lean)
- [DataTypesAsLattices/Functionality/theorem_7_3_iii.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_3_iii.lean)
- [DataTypesAsLattices/Functionality/theorem_7_4.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_4.lean)
- [DataTypesAsLattices/Functionality/theorem_7_4_finite.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_4_finite.lean)
- [DataTypesAsLattices/Functionality/theorem_7_4_i.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_4_i.lean)
- [DataTypesAsLattices/Functionality/theorem_7_4_plotkin.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_4_plotkin.lean)
- [DataTypesAsLattices/Functionality/theorem_7_4_sigma_index.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_4_sigma_index.lean)
- [DataTypesAsLattices/Functionality/theorem_7_4_unique.lean](DomainTheory/DataTypesAsLattices/Functionality/theorem_7_4_unique.lean)
- [DataTypesAsLattices/Functionality/treeF_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Functionality/treeF_isScottContinuous.lean)
- [DataTypesAsLattices/Functionality/treeR_fixedPoint.lean](DomainTheory/DataTypesAsLattices/Functionality/treeR_fixedPoint.lean)
- [DataTypesAsLattices/Functionality/treeR_isRetract.lean](DomainTheory/DataTypesAsLattices/Functionality/treeR_isRetract.lean)
- [DataTypesAsLattices/Functionality/tree_atom.lean](DomainTheory/DataTypesAsLattices/Functionality/tree_atom.lean)
- [DataTypesAsLattices/Functionality/tree_node.lean](DomainTheory/DataTypesAsLattices/Functionality/tree_node.lean)
- [DataTypesAsLattices/Functionality/typed_apply_retract.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_apply_retract.lean)
- [DataTypesAsLattices/Functionality/typed_bot_bot.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_bot_bot.lean)
- [DataTypesAsLattices/Functionality/typed_bot_botElem.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_bot_botElem.lean)
- [DataTypesAsLattices/Functionality/typed_bot_lamb.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_bot_lamb.lean)
- [DataTypesAsLattices/Functionality/typed_env_nth.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_env_nth.lean)
- [DataTypesAsLattices/Functionality/typed_inleft_int_lamb.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_inleft_int_lamb.lean)
- [DataTypesAsLattices/Functionality/typed_inright_arrow_lamb.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_inright_arrow_lamb.lean)
- [DataTypesAsLattices/Functionality/typed_isGraph.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_isGraph.lean)
- [DataTypesAsLattices/Functionality/typed_ofNat_intR.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_ofNat_intR.lean)
- [DataTypesAsLattices/Functionality/typed_pairSeq_tensorR.lean](DomainTheory/DataTypesAsLattices/Functionality/typed_pairSeq_tensorR.lean)
- [DataTypesAsLattices/Functionality/updateEnvUnion.lean](DomainTheory/DataTypesAsLattices/Functionality/updateEnvUnion.lean)
- [DataTypesAsLattices/Functionality/updateEnvUnion_isScottContinuous_idx.lean](DomainTheory/DataTypesAsLattices/Functionality/updateEnvUnion_isScottContinuous_idx.lean)
- [DataTypesAsLattices/Functionality/updateEnvUnion_isScottContinuous_t.lean](DomainTheory/DataTypesAsLattices/Functionality/updateEnvUnion_isScottContinuous_t.lean)
- [DataTypesAsLattices/Functionality/updateEnvUnion_ofNat.lean](DomainTheory/DataTypesAsLattices/Functionality/updateEnvUnion_ofNat.lean)
- [DataTypesAsLattices/Functionality/updateEnv_isScottContinuous_t.lean](DomainTheory/DataTypesAsLattices/Functionality/updateEnv_isScottContinuous_t.lean)
- [DataTypesAsLattices/Functionality/whichC.lean](DomainTheory/DataTypesAsLattices/Functionality/whichC.lean)
- [DataTypesAsLattices/Functionality/whichC_app.lean](DomainTheory/DataTypesAsLattices/Functionality/whichC_app.lean)
