# Computability in effectively given domains

For the domain $N$ the strict functions from $N$ into $N$, the strict maps $f : N \to N$, correspond exactly to the partial functions $g : N \to N$ (as we wrote in 5.6 we had $f = \bar{g}$). For such functions there is a standard theory of computability: $g$ is called computable if it can be defined as a partial recursive function with its "program" written down in a certain standard form. The non-strict maps $h : N \to N$ are all constant, and so are intuitively computable; so we know all about computable maps in $|N \to N|$ in general. The question is: what are the computable maps on (elements of) other domains?

The answer will of course depend on how the domain is presented to us. Even with $N$, there are continuum many isomorphisms $\pi : N \to N$ of $N$ onto itself, not all of which can be computable. That is, if we permute $N$ and, so to speak, present the integers in a different order, then a well-behaved computable function $f : N \to N$ may well be transformed into a non-computable function,

$$
\pi \circ f \circ \pi^{-1} : N \to N.
$$

(Hint: Consider the characteristic function $e$ of the even numbers. Take $f = \bar{e}$ and let $\pi$ be very horrid.) The reason we imagined we knew which were the computable $f : N \to N$ is that $N$ is always thought of in a standard presentation. We must thus define "in general" a concept of an *effectively given domain*, that is to say, one with a sufficiently computable presentation to represent the additional knowledge about the domain.

The main idea will be that the *finite elements* of $|D|$ should be regarded as the ones initially known. Abstractly, to know a finite element is to know how it is *related* to other finite elements.
Of course, this will mean that we will allow at most a countable infinity of finite elements — but this restriction well accords with intuition. To make precise the terminology "related to" it proves most convenient to go back to the neighbourhoods (in any case they are in a one-one correspondence with the finite elements).

**DEFINITION 7.1.** A neighbourhood system $D$ has a *computable presentation* provided we can write

$$D = \{ X_n \mid n \in N \},$$

where the following two relations

(i) $X_n \cap X_m = X_k \ ;$ and

(ii) $\exists k \in N \ldotp X_k \subseteq X_n$ and $X_k \subseteq X_m$

are recursively decidable (in integer indices $n, m, k$ and in $n, m$, respectively). $\square$

More strictly the sequence,

$$\langle X_n \rangle_{n=0}^{\infty},$$

is the presentation. Even more strictly, when it is required to cope with infinitely many domains at a time, it would be necessary to give the actual Gödel numbers of the recursive relations (i) and (ii) (rather than just saying there exists some way of showing them to be recursively decidable).

The intuitive idea of 7.1 is that the system is effectively given if you know how to do elementary "calculations" with neighbourhoods. The basic calculations are the forming of intersections. The neighbourhoods have to be laid out in a systematic way; and, if we are asked for an intersection of two given neighbourhoods, we have to be able to locate it in the standard sequence. Relation (ii) is the *consistency condition* , which is the necessary and sufficient condition for the intersection to exist in $D$. When (ii) is true, therefore, we have only to try $k = 0, 1, 2, \ldots$ until we discover that we have found the intersection. We are
assuming that these basic decisions can be carried out in "finite time". Note that the obvious biconditional,

$$X_n \subseteq X_m \text{ iff } X_n \cap X_m = X_n,$$

assures us that the inclusion relation between neighbourhoods is itself decidable in terms of the indices. So in (ii) if $k$ exists, *then* it (or the first one) can indeed be found in finite time. The rub is that if it *does not exist*, no finite number of inclusion checks will determine that fact. That is why we have to *assume* that (ii) is always decidable. The information contained in (ii) is a fundamental part of the neighbourhood structure. (An axiomatic characterization of neighbourhood structures is given in Exercise 7.13, which may make clearer what we are assuming and what a presentation is.)

**DEFINITION 7.2.** Given two recursively presented domains,

$$\mathcal{D} = \{ X_n \mid n \in \mathbf{N} \} \text{ and } E = \{ Y_m \mid m \in \mathbf{N} \},$$

an approximable mapping $f : \mathcal{D} \to E$ is said to be *computable* iff the relation

$$X_n f Y_m$$

is recursively enumerable in $n$ and $m$. $\square$

The question to ask first is why "recursively enumerable" rather than "recursive" (= "recursively decidable")? The answer will become clear when we let $\mathcal{D}$ degenerate to the one-element domain, $\mathcal{D} = \{ \Delta \}$. Then what we are considering is merely a single element

$$y = f(\{ \Delta \}) \in |E|.$$

Therefore, 7.2 incorporates the notion of a *computable element* of a domain. And the condition reduces to the statement that the filter $y \in |E|$ is such that the set

$$\{ m \in \mathbf{N} \mid Y_m \in y \}$$

is a recursively enumerable set of integers. The point is that the elements of $|E|$ are finite or infinite. If $y$ were finite, the set of indices above would indeed be recursive in view of
our assumptions on $E$. But an infinite element can in general only be approximated "a little at a time". We cannot expect to know the whole story of its approximations in a flash. What it means to be recursively enumerable is that there is a primitive recursive function (hence, a total function), $r : \mathbf{N} \to \mathbf{N}$, such that

$$y = \{ Y_{r(i)} \mid i \in \mathbf{N} \}.$$

That is to say, *all* the approximations to $y$ can eventually be listed. In the case of the mapping $f$ we could write

$$f = \{ (X_{s(i)}, Y_{r(i)}) \mid i \in \mathbf{N} \},$$

for a suitable pair of primitive recursive functions $s$ and $r$.

Definitions 7.1 and 7.2 may very well irritate the person hearing them for the first time: instead of explaining computability in direct terms, the whole question is thrown into the lap of recursion theory! There are several answers. "You have to start somewhere" is one thing I always say. Recursion on the integers is a well-understood theory, and we shall not need the refined parts of the development, fortunately. In any case, our definitions apply to *many* domains of quite different structure, not just to the domain $\mathbf{N}$. And the next step we shall take is to show how to build up computable functions (and also effectively given domains) from simpler ones. Thus, often it will not be necessary to go back to the seemingly over-precise definitions involving the indices but to appeal to some broad general principles.

**PROPOSITION 7.3.** The identity map on an effectively given domain is computable; the composition of computable mappings on effectively given domains is again computable. $\square$

The proofs for 7.3 are so trivial they are hardly worth an exercise. Note the immediate and useful consequence: if $f : D \to E$ is computable and $x \in |D|$ is computable, then $f(x) \in |E|$ is also computable. The next result is, however, worth working out even though it is quite easy.
**THEOREM 7.4.** If $\mathcal{D}_0$ and $\mathcal{D}_1$ are effectively given, then so are $(\mathcal{D}_0 + \mathcal{D}_1)$ and $(\mathcal{D}_0 \times \mathcal{D}_1)$.

Moreover the combinators $\mathrm{in}_i$ and $\mathrm{out}_i$ and $\mathrm{proj}_i^2$ are all computable; further, if $f$ and $g$ are computable maps, then so are $f + g$ and $f \times g$.

*Proof:* Let the computable presentations be given as:

$$\mathcal{D}_i = \{ X_n^i \mid n \in \mathbf{N} \}.$$

We can assume that the sets of tokens $\Delta_0$ and $\Delta_1$ are disjoint and $\emptyset \notin \mathcal{D}_i$. Then the construction of the sum is just

$$\mathcal{D}_0 + \mathcal{D}_1 = \{ \Delta_0 \cup \Delta_1 \} \cup \mathcal{D}_0 \cup \mathcal{D}_1.$$

As an enumeration we define for $n \in \mathbf{N}$:

$$Z_0 = \Delta_0 \cup \Delta_1 \ ; \ Z_{2n+1} = X_n^0 \ ; \ Z_{2n+2} = X_n^1 \ .$$

We leave as an exercise the check of 7.1(i)–(ii).

For the product we want:

$$\mathcal{D}_0 \times \mathcal{D}_1 = \{ X_n^0 \cup X_m^1 \mid n, m \in \mathbf{N} \}.$$

What we then need are recursive functions $p : \mathbf{N} \to \mathbf{N}$, $q : \mathbf{N} \to \mathbf{N}$, and $r : \mathbf{N} \times \mathbf{N} \to \mathbf{N}$ where for $m, n, k \in \mathbf{N}$ we have:

$$p(r(n, m)) = n \text{ and } q(r(n, m)) = m, \text{ and } r(p(k), q(k)) = k.$$

Thus $r$ is a "one-one pairing function"; there are many ways to find such functions (see Exercise 5.13). We can then define for $k \in \mathbf{N}$:

$$W_k = X_{p(k)}^0 \cup X_{q(k)}^1 \ .$$

Again we leave as an exercise the check that this provides a computable presentation of $\mathcal{D}_0 \times \mathcal{D}_1$.

As for the combinators, the neighbourhood relations have to be worked out in terms of the indices. For example

$$X_n^0 \ \mathrm{in}_0 \ Z_m \text{ iff either } m = 0 \text{ or for some } k$$

$$m = 2k + 1 \text{ and } X_n^0 \subseteq X_k^0 \ .$$

and

$$W_k \ \mathrm{proj}_1^2 \ X_m^1 \text{ iff } X_{q(k)}^1 \subseteq X_m^1 \ .$$

The reader needs to check that these are recursively enumerable
Relations in the indices. For this purpose it may be convenient to recall some closure properties of these relations: taking conjunctions, disjunctions, substituting recursive functions, applying an existential quantifier to the front. $\square$

Products give us a way of providing an immediate meaning to the notion of a computable function of several variables. Note that the proof of 3.7 is “effective” and shows that substitution of computable functions of several variables into each other always gives computable functions. We turn next to the function spaces.

**THEOREM 7.5.** If $\mathcal{D}_0$ and $\mathcal{D}_1$ are effectively given, then so is $(\mathcal{D}_0 \to \mathcal{D}_1)$. The combinators eval and curry are computable, provided all the domains involved are effectively given. The computable elements $f \in |\mathcal{D}_0 \to \mathcal{D}_1|$ are exactly the computable maps $f : \mathcal{D}_0 \to \mathcal{D}_1$.

*Proof:* The proofs of 3.9, 3.11, and 3.12 were set up with this theorem in mind. If
$$
\mathcal{D}_0 = \{ X_n \mid n \in \mathbf{N} \} \quad \text{and} \quad \mathcal{D}_1 = \{ Y_m \mid m \in \mathbf{N} \}
$$
are two effectively given neighbourhood systems, then the neighbourhoods of $(\mathcal{D}_0 \to \mathcal{D}_1)$, by Definition 3.8, are non-empty intersections like
$$
\bigcap_{i < q} [X_{n_i}, Y_{m_i}],
$$
where $\langle n_0, n_1, \ldots, n_{q-1} \rangle$ and $\langle m_0, m_1, \ldots, m_{q-1} \rangle$ are two finite sequences of integers determining the choice of the function-space neighbourhood. In 3.9(i) the test for nonemptiness is given. Assuming the decidability of relations in $\mathcal{D}_0$ and $\mathcal{D}_1$, one remarks that the consistency of *finite sequences* of neighbourhoods is also decidable. (Hint: Test the first *two*, then form their intersection. Next test the third given neighbourhood against this one set; if consistent, form the intersection, and carry on.) By 3.9(i) at most $2 \cdot 2^q$ such sequential checks must be carried out to determine whether the function-space neighbourhood is non empty.
It may not be fun, but the checks can be carried out in finite time. Owing to this decidability, we can therefore enumerate in a systematic way *all* the pairs of finite sequences $\langle n_0, \ldots \rangle$ and $\langle m_0, \ldots \rangle$ that determine neighbourhoods: that is the way that $(\mathcal{D}_0 \to \mathcal{D}_1)$ obtains its enumeration.

Concerning the decidability of the required relations on $(\mathcal{D}_0 \to \mathcal{D}_1)$, we remark first off that consistency is more of the same: to test two finite intersections against each other, just form one big intersection and test it for non-emptiness as before. Secondly, the testing for intersection comes down in the end to testing one typical intersection of $[X, Y]$-neighbourhoods for equality with another. But equality amounts to two inclusions; inclusion in an intersection amounts to inclusion in each term. Therefore, what we need to do is to check a finite number of statements of the form:

$$\bigcap_{i < q} [X_{n_i}, Y_{m_i}] \subseteq [X_k, Y_\ell].$$

As we pointed out after the proof of 3.9, this inclusion is equivalent to

$$\bigcap \{ Y_{m_i} \mid X_k \subseteq X_{n_i} \} \subseteq Y_\ell.$$

By decidability in $\mathcal{D}_0$, we can effectively find the $n_i$ that are needed. Then in $\mathcal{D}_1$, we form the intersection of the corresponding $Y_{m_i}$. Finally, we check the inclusion. Again, one check in $(\mathcal{D}_0 \to \mathcal{D}_1)$ requires a whole sequence of checks in $\mathcal{D}_0$ and in $\mathcal{D}_1$, but the process is finite. So we have argued that $(\mathcal{D}_0 \to \mathcal{D}_1)$ is effectively given.

In showing that the combinators are computable, we refer first to the proof of 3.11. The typical pair of neighbourhoods possibly belonging to eval is

$$\bigcap_{i < q} [X_{n_i}, Y_{m_i}], \ X_k \text{ eval } Y_\ell.$$

As we needed not to be so specific, we expressed the holding of this relationship in terms of *all* the functions in the function-
space neighbourhood. But we know that the neighbourhood, by 3.9(ii), has a minimal element; it is then sufficient to test for the holding of $X_k f_0 Y_\ell$ at this minimal function $f_0$. But this test, we have already seen, is decidable. So the pairs in eval actually form a recursive set, not just a recursively enumerable set; thus, eval is a computable function.

The case of curry involves three domains and is a bit more messy. But again, if the required neighbourhoods are written out in full, it will be seen that curry, too, is computable. We leave this minor struggle to the exercises.

The final statement is an easy consequence of the fundamental connection between approximable $f : \mathcal{D}_0 \to \mathcal{D}_1$ as relations and as elements. Recall, as in the proof of 3.10, that we have

$$f \in [X, Y] \text{ iff } X f Y,$$

for all $X \in \mathcal{D}_0$ and $Y \in \mathcal{D}_1$. Therefore,

$$f \in \bigcap_{i < q} [X_{n_i}, Y_{m_i}] \text{ iff } \forall i < q.\, X_{n_i} f Y_{m_i}.$$

It follows that if $f$ is recursively enumerable as a set of pairs, then, by forming all the non-empty intersections (as shown), we get an enumeration of all the neighbourhoods to which $f$ belongs; and this is the same as the filter corresponding to $f$ as an element of the function space. The converse direction is clear. $\square$

We have nearly all our favourite combinators computable, but perhaps the most important one - since it is the key to recursive definitions - is the fixed-point combinator. It is not left out.

**THEOREM 7.6.** For any effectively given domain $\mathcal{D}$, the combinator $\mathrm{fix} : (\mathcal{D} \to \mathcal{D}) \to \mathcal{D}$ is computable.

*Proof :* Referring back to the proof of Theorem 4.2 and thinking of

$$\mathcal{D} = \{ X_n \mid n \in \mathbb{N} \}$$

as effectively given, fix as a relation comes down to
$$\bigcap_{i < q} [X_{n_i}, X_{m_i}] \text{ fix } X_\ell \text{ iff for some finite sequence}$$

$$\Delta = X_{k_0}, \ldots, X_{k_p} = X_\ell,$$

we have, for each $j < p$,

$$\bigcap \{ X_{m_i} \mid X_{k_j} \subseteq X_{n_i} \} \subseteq X_{k_{j+1}}.$$

Inside the “for some finite sequence” all the checks are decidable by assumption on $D$. But the existential quantification of a decidable predicate always gives a recursively enumerable predicate. (And, as there is no implied bound on the size of the finite sequence we are looking for, this really *is* an enumerable set and not generally a recursive set.) $\square$

The major consequence of what we have done up to this point concerns typed $\lambda$-calculus. Any expression involving only *effectively given types* and, perhaps, some *basic computable constants* using only the $\lambda, !$-notation defines a computable function of its free variables. And such functions applied to computable arguments give computable values. And such functions have computable least fixed points. Etc., etc. In a definite sense then we have in the “metalanguage”, as people say, a quite precise and fully *mathematical programming language* for defining computable operators. It is not a machine implemented language, but it is a mathematically well-defined and easy-to-use language. And when we combine the usual type-definition facility together with *domain equations*, we have an especially powerful language.

**PROPOSITION 7.7.** For any effectively given domain $D$, the domain $D^\S$ is also effectively given, and all the combinators of Example 6.1 prove to be computable.

*Proof:* This proof is essentially an exercise, but it is useful to have an easy-to-grasp example. Indeed, to make things easy to reason about, we can assume that $D$ is a system over $\Delta = \mathbf{N}$, and that in the presentation where

$$D = \{ X_n \mid n \in \mathbf{N} \},$$

the relation $k \in X_n$ is *recursive* in $k$ and $n$. (It is worth thinking why this is so.) Of course, a lot of other things are recursive also.
Now what kind of a system is $D^\S$? The construction of 6.1 made it a system over a certain set of strings $\Gamma$. For the sake of checking various assertions about computability, we are transposing everything back to $\mathbf{N}$. (These are all denumerable sets in any case.) The set $\Gamma$ is divided into three equally big parts, and we can do the same for $\mathbf{N}$. Let us write for any $m, k \in \mathbf{N}$ and subset $X \subseteq \mathbf{N}$:

$$mX + k = \{ m \cdot n + k \mid n \in X \}.$$

Then by splitting the integers modulo 3 we have:

$$\mathbf{N} = 3\mathbf{N} \cup (3\mathbf{N} + 1) \cup (3\mathbf{N} + 2),$$

and this equation is quite analogous to that for $\Gamma$. We then propose this definition for $D^\S$:

$$D^\S = \{\mathbf{N}\} \cup \{3X \mid X \in D\} \cup \{(3X + 1) \cup (3Y + 2) \mid X, Y \in D^\S\},$$

but this does not make the enumeration of $D^\S$ all that obvious. This is one way to do it:

$$V_0 = \mathbf{N} \ ; \ V_{2n+1} = 3X_n \ ; \ V_{2n+2} = (3V_{p(n)} + 1) \cup (3V_{q(n)} + 2).$$

Here $p$ and $q$ are the inverse of the pairing functions mentioned in 7.4. They must be chosen so that $p(n) < n$ and $q(n) < n$ for all $n \in \mathbf{N}$. Thus, in calculating $V_k$ where $k = 2n + 2$ we will be using $V_{p(n)}$ and $V_{q(n)}$ where both subscripts are strictly less than $k$. This observation is required so that $m \in V_k$ is going to be a recursive relation. What we claim is that

$$D^\S = \{V_k \mid k \in \mathbf{N}\}.$$

It should be clear that everything on the right belongs to $D^\S$. What needs an inductive argument is that everything in $D^\S$ is eventually of the form $V_k$. But this should be fairly obvious owing to the properties of $r : \mathbf{N} \times \mathbf{N} \leftrightarrow \mathbf{N}$.

The reader also has to check that 7.1(i)–(ii) hold for the $V_k$. The idea is that any such check is either (1) trivial, or (2) something already assumed about $D$ and the $X_n$, or (3) can be thrown back to some sets $V_m$ with strictly smaller subscripts. Therefore, the checks will give an answer in finite time according to an effective reduction.

Next for the combinators, we have to translate neighbourhood relations into relations among integer indices. A selection of examples must suffice,

$$X_n\ (\lambda x.\, x^\S)\ V_k \text{ iff } V_{2n+1} \subseteq V_k$$
$$V_m \ \mathrm{proj}_0 \ V_k \text{ iff } k = 0 \text{ or } \exists n \in \mathbf{N}.\, m = 2n + 2 \text{ and } V_{p(n)} \subseteq V_k.$$

The reader should write out other cases. $\square$

**EXAMPLE 7.8.** We have often made reference to the powerset $P\mathbf{N}$ as a domain and we should check here that it is effectively given. One easy way to see this is to note

$$P\mathbf{N} \cong |T^\infty|.$$

The (slight) trouble with $P\mathbf{N}$ is that we usually think of it in terms of *elements* rather than *neighbourhoods*. Going back to Exercise 1.16, we can argue that the neighbourhoods of $P\mathbf{N}$ are ordered not like the finite sets of integers but in the partial ordering *converse* to that. But this is of no trouble, since all will be decidable. What we need first is an enumeration of all finite sets of integers. We can do this by:

$$E_n = \{ k \mid \exists i, j.\, i < 2^k \text{ and } n = i + 2^k + j \cdot 2^{k+1} \}.$$

The idea is that $k \in E_n$ means that the exponent $k$ does occur in the binary expansion of $n$ as a sum of powers of 2. All finite subsets of $\mathbf{N}$ are of the form $E_n$. We then find that as a neighbourhood system

$$(P\mathbf{N}) = \{ \mathbf{N} \setminus E_n \mid n \in \mathbf{N} \}.$$

As the relationship $E_n \cup E_m = E_k$ is recursive, there is no trouble in proving that this is a computable presentation. In this system, of course, any two neighbourhoods are consistent. Various combinators on $P\mathbf{N}$ are suggested in Exercise 7.23. $\square$

We end this chapter with an example of another kind of domain construct. This construct is known as the *Smyth Power Domain*. It is defined for any neighbourhood system $\mathcal{D}$ and results in a new system we shall call here $\mathbb{P}\mathcal{D}$. The elements of $\mathbb{P}\mathcal{D}$ behave rather like *sets of elements* of $\mathcal{D}$, but since our elements can be either partial or total, there are certain dangers to pushing the analogy too far. For some purposes a rival construct called the *Plotkin Power Domain* is better, but it leads outside the category of neighbourhood systems as defined in these lectures. Do not confuse $P\mathbf{N}$ with $\mathbb{P}\mathcal{D}$.
**DEFINITION 7.9.** Let $\mathcal{D}$ be any neighbourhood system and define

$$\mathbb{P}\mathcal{D} = \left\{ \bigcup_{i < n} (\downarrow X_i) \mid \forall i < n.\, X_i \in \mathcal{D} \right\}.$$

We recall that for any $X \in \mathcal{D}$

$$\downarrow X = \{ Y \in \mathcal{D} \mid Y \subseteq X \}.$$

The finite unions in $\mathbb{P}\mathcal{D}$ can be empty (i.e. if $n = 0$). $\square$

Formally, the system $\mathbb{P}\mathcal{D}$ is just more or less the closure of $\mathcal{D}$ under finite unions; however, this would not be an isomorphism-invariant construct unless $\mathcal{D}$ is "prepared". The preparation consists of replacing $\mathcal{D}$ by the isomorphic domain

$$\mathcal{D}^\dagger = \{ \downarrow X \mid X \in \mathcal{D} \}.$$

(In this connection refer back to Exercise 1.20.) We remark that

$$\downarrow X \cap \downarrow Y \neq \emptyset \text{ iff } \{X, Y\} \text{ is consistent in } \mathcal{D},$$

and in that case

$$\downarrow X \cap \downarrow Y = \downarrow (X \cap Y).$$

**PROPOSITION 7.10.** The power domain $\mathbb{P}\mathcal{D}$ is a neighbourhood system if $\mathcal{D}$ is, and it is effectively given if $\mathcal{D}$ is.

*Proof* : The system $\mathcal{D}^\dagger$ is a neighbourhood system as we just remarked; indeed it is a positive neighbourhood system. It is easy to prove that the closure of any positive system under finite unions is a neighbourhood system, because the resulting family of sets is closed under *all* finite intersections. (If we left out the empty union, the result would be a positive system.) The proof is obvious since intersection of sets distributes over finite union. So $\mathbb{P}\mathcal{D}$ is a neighbourhood system.

For the second half of the proposition, we just have to constructivize the previous argument. Thus, if

$$\mathcal{D} = \{ X_n \mid n \in \mathbb{N} \},$$

then the elements of $\mathbb{P}\mathcal{D}$ can be written as:

$$\bigcup_{i < q} (\downarrow X_{n_i}),$$
and hence are indexed by the finite sequences $\langle n_0, \dots, n_{q-1} \rangle$ of integers. Now one of the standard devices of recursion theory is to put the finite sequences of integers into a recursive one-one correspondence with the integers themselves. This is the start of the recursive presentation of $\mathbb{P}\mathcal{D}$, since it means we can list effectively all the required neighbourhoods.

Next consider an intersection

$$\bigcup_{i < q} (\downarrow X_{n_i}) \cap \bigcup_{j < r} (\downarrow X_{m_j}) = \bigcup_{\substack{i < q \\ j < r}} \downarrow (X_{n_i} \cap X_{m_j}) \, .$$

Some of the terms which are $\emptyset$ have to be thrown out — but this requires only a finite number of decisions all computable by assumption. Now we have to rewrite

$$X_{n_i} \cap X_{m_j} = X_{k_{ij}} \, ,$$

but the finding of $k_{ij}$ is also computable. *Finally*, we have to re-order the doubly indexed sequence into a singly indexed sequence of length $q \cdot r$, but this is easily seen to be computable also. Therefore, intersections can be "calculated".

It remains to be shown that equality between neighbourhoods in $\mathbb{P}\mathcal{D}$ is decidable. The question really comes down to deciding something like:

$$\downarrow X_k \subseteq \bigcup_{i < q} \downarrow X_{n_i} \, .$$

Now since $X_k \in \downarrow X_k$, we find that the above is just equivalent to:

$$\exists i < q \ldotp X_k \subseteq X_{n_i} \, .$$

By our assumptions on $\mathcal{D}$, this is decidable. (It is this part of the argument that required the passage to $\mathcal{D}^\dagger$. It does not seem to be generally true that the closure under finite unions of an effectively given system is again effectively given.) $\square$

One of the main reasons that $\mathbb{P}\mathcal{D}$ is like a power domain is the possibility of forming "finite sets".
**DEFINITION 7.11.** For elements $x_0, \dots, x_{n-1} \in |D|$ we define

$$\{x_0, \dots, x_{n-1}\} = \{z \in \mathbb{P} D \mid \exists X_0 \in x_0 \dots \exists X_{n-1} \in x_{n-1}.\, \bigcup_{i<n} (\uparrow X_i) \subseteq z\}.$$

(Note, we could also write $\forall i < n.\, X_i \in z$.) $\square$

**PROPOSITION 7.12.** The mapping

$$\lambda x_0, \dots, x_{n-1}.\, \{x_0, \dots, x_{n-1}\} : D^n \to \mathbb{P} D$$

is approximable and is computable if $D$ is effectively given. Moreover, the map $\lambda x.\, \{x\}$ shows that $D \trianglelefteq \mathbb{P} D$, and we also have the law:

$$\{x_0, \dots, x_{n-1}\} = \{x_0\} \cap \dots \cap \{x_{n-1}\}$$

as an intersection of filters.

*Proof* : The second part shows that everything reduces to $\lambda x.\, \{x\}$. We see that

$$X_k\ (\lambda x.\, \{x\})\ \bigcup_{i<q} (\uparrow X_{n_i}) \text{ iff } \exists i < q.\, X_k \sqsubseteq X_{n_i}.$$

Thus, $\lambda x.\, \{x\}$ is an approximable mapping and is computable in the effectively given case.

The proof of the law can be reduced to the special case

$$\{x\} \cap \{y\} = \{x, y\}$$

for the sake of illustration. In terms of finite elements of the two domains $D$ and $\mathbb{P} D$ we find

$$\{\uparrow X\} = \uparrow\uparrow X,$$

and so,

$$\begin{aligned}
\{\uparrow X\} \cap \{\uparrow Y\} &= \uparrow\uparrow X \cap \uparrow\uparrow Y \\
&= \uparrow(\uparrow X \cup \uparrow Y) \\
&= \{\uparrow X, \uparrow Y\}.
\end{aligned}$$

An equation between approximable functions that checks for finite elements also holds for all elements.

Finally, we note that

$$D \cong D^\dagger \trianglelefteq \mathbb{P} D$$
and that the isomorphism involved is just $\lambda x.\,\{x\}$ by what we saw on the finite elements. $\square$

Further combinators on the power domain are given in the exercises.

## EXERCISES

**EXERCISE 7.13.** Show that an effectively given domain can always be identified with a relation $\mathrm{INCL}(n,m)$ on integers, where the two derived relations

$$\mathrm{CONS}(n,m) \text{ iff } \exists k.\,\mathrm{INCL}(k,n) \text{ and } \mathrm{INCL}(k,m);$$

$$\mathrm{MEET}(n,m,k) \text{ iff } \forall j\,[\mathrm{INCL}(j,k) \text{ iff } \mathrm{INCL}(j,n) \text{ and } \mathrm{INCL}(j,m)]$$

are both recursively decidable, and where the following axioms hold:

(i) $\forall n.\,\mathrm{INCL}(n,n);$

(ii) $\forall n,m,k.\,\mathrm{INCL}(n,m)$ and $\mathrm{INCL}(m,k)$ imply $\mathrm{INCL}(n,k);$

(iii) $\exists m\,\forall n.\,\mathrm{INCL}(n,m)$

(iv) $\forall n,m.\,\mathrm{CONS}(n,m)$ implies $\exists k.\,\mathrm{MEET}(n,m,k).$

(Hint: Consider the neighbourhood system

$$\mathcal{D} = \big\{ \{m \in \mathbf{N} \mid \mathrm{INCL}(m,n)\} \mid n \in \mathbf{N} \big\}.$$

Is this essentially any effectively given system?)

**EXERCISE 7.14.** (For recursive-function theorists.) Prove the statements after definition 7.2 about the existence of primitive recursive functions for showing things recursively enumerable. (Recall that a non-empty set is r.e. iff it is the range of a primitive recursive function.) Show also that every computable element $y \in |E|$ can be written

$$y = \bigcup \{ \uparrow Y_{t(i)} \mid i \in \mathbf{N} \},$$

where $t : \mathbf{N} \to \mathbf{N}$ is primitive recursive and where we may assume
$Y_{t(i+1)} \subseteq Y_{t(i)}$

for all $i \in \mathbf{N}$.

**EXERCISE 7.15.** Finish the proof of 7.4 and establish similar results for the constructs $(D_0 \otimes D_1)$, $(D_0 \oplus D_1)$ and $D^\infty$. Take into account the various appropriate combinators.

**EXERCISE 7.16.** Let $D_0 = \{ X_n \mid n \in \mathbf{N} \}$, $D_1 = \{ Y_m \mid m \in \mathbf{N} \}$ and $D_2 = \{ Z_k \mid k \in \mathbf{N} \}$ be three effectively given domains. Complete the proof of 7.5 by writing out curry as a relation between neighbourhoods. Is it a recursive set or only a recursively enumerable set?

**EXERCISE 7.17.** Complete the proof of 7.7 for showing that $D^{\S}$ is effectively given if $D$ is. Include all the combinators of 6.2. Prove also that if $E$ is effectively given and $u : D \to E$ and $v : E \times E \to E$ are computable, then the unique strict mapping $g : D^{\S} \to E$, where, for $x \in |D|$ and $y, z \in |E|$,

$$g(\mathrm{in}(x)) = u(x), \quad \text{and}$$

$$g(\mathrm{pair}(y, z)) = v(g(y), g(z)),$$

is a computable mapping.

**EXERCISE 7.18.** Two effectively given systems $D$ and $E$ are *effectively isomorphic* iff … (complete the sentence!). Show that if $D$ is effectively given then the isomorphism

$$D^\infty \cong (D^\infty)^\infty$$

is effective.
**EXERCISE 7.19.** Prove that $D \mapsto \mathbb{P} D$ is a functor by defining for each $f : D \to E$ a mapping

$$\mathbb{P} f : \mathbb{P} D \to \mathbb{P} E$$

by the formula

$$\bigcup_{i < n} \downarrow X_i \quad \mathbb{P} f \quad \bigcup_{j < m} \downarrow Y_j \quad \text{iff} \quad \forall i < n \exists j < m.\, X_i f Y_j \, .$$

Be sure to check that $\mathbb{P} f$ is approximable and that $\mathbb{P}$ preserves identity maps and composition. If $f$ is computable, is $\mathbb{P} f$? Is there a combinator $\lambda f.\, \mathbb{P} f$? What is

$$\mathbb{P} f(\{x, y\}) = ??$$

**EXERCISE 7.20.** Show that there is a combinator

$$\text{union} : \mathbb{P}(\mathbb{P} D) \to \mathbb{P} D$$

where for suitable neighbourhoods

$$\bigcup_{i < n} \downarrow \Bigl(\bigcup_{j < m_i} \downarrow X_{ij}\Bigr) \quad \text{union} \quad \bigcup_{k < q} \downarrow Y_k \quad \text{iff} \quad \forall i < n \forall j < m_i \exists k < q.\, X_{ij} \subseteq Y_k \, .$$

Is union computable if $D$ is effectively given? What is

$$\text{union}(\{\{x\}, \{y, z\}\}) = ??$$

Are $\mathbb{P}(\mathbb{P} D)$ and $\mathbb{P} D$ generally isomorphic??

**EXERCISE 7.21.** Is there a non-trivial combinator of type

$$\mathbb{P}(D \to E) \to (\mathbb{P} D \to \mathbb{P} E)\ ?$$

Are there in general any isomorphisms between the systems

$$(D \to \mathbb{P} E),\, \mathbb{P}(D \times E),\, \mathbb{P} D \times \mathbb{P} E\ ??$$

Is there a non-trivial combinator of type

$$\mathbb{P}(D \times E) \times \mathbb{P}(E \times F) \to \mathbb{P}(D \times F)\ ???$$

Is there any connection between

$$\mathbb{P}\mathbf{N} \text{ and } P\mathbf{N}\ ????$$
**EXERCISE 7.22.** (For algebraists.) Let $\Sigma = \{0,1\}^*$ be the free semigroup. A new domain is constructed by defining a family of sets by the least fixed point theorem as follows:

$$S = \{\Sigma\} \cup \{\{\sigma\} \mid \sigma \in \Sigma\} \cup \{XY \mid X, Y \in S\} \cup \{X \cap Y \mid X, Y \in S \text{ and } X \cap Y \neq \emptyset\}.$$

Here we write: $XY = \{\sigma\tau \mid \sigma \in X \text{ and } \tau \in Y\}$.

Prove that $S$ is an effectively given, positive neighbourhood system. (Hint: The sets in $S$ are each “regular events” in the terminology of automata theory, and we have a decision method for the set algebra of regular events.)

Define multiplication on $|S|$ by

$$xy = \{Z \in S \mid \exists X \in x \ \exists Y \in y.\ XY \subseteq Z\},$$

and show $|S|$ becomes a semigroup with $\Sigma$ embedded into $|S|$ by the homomorphism $\sigma \mapsto \{X \in S \mid \sigma \in X\}$.

Investigate some *infinite words* in $S$, say those defined by least fixed points such as: $\vec{\sigma} = \sigma\,\vec{\sigma}$ and $\vec{\sigma} = \vec{\sigma}\,\sigma$. Are these equations true:

$$\vec{\sigma}\,\vec{\sigma} = \vec{\sigma}, \quad \vec{\sigma}\,\vec{\sigma}\,\vec{\sigma} = \vec{\sigma}, \quad \vec{\sigma}\,\vec{1}\,\vec{\sigma}\,\vec{1} = \vec{\sigma}\,\vec{1},$$

and $\vec{01}\,\vec{01}\,\vec{01}\,\vec{01} = \vec{01}\,\vec{01}$ ?

**EXERCISE 7.23.** Complete the discussion of $P\mathbf{N}$ of Example 7.8. Show that the combinators $\mathrm{fun}$ and $\mathrm{graph}$ of Exercise 5.14 are computable. Also do the same for

$$\lambda x, y.\, x \cap y, \quad \lambda x, y.\, x \cup y, \quad \text{and } \lambda x, y.\, x + y,$$

where for $x, y \in P\mathbf{N}$ we define

$$x + y = \{n + m \mid n \in x \text{ and } m \in y\}.$$

What are the computable elements of $P\mathbf{N}$ ?
**EXERCISE 7.24.** (Suggested by the LUCID language of Ashcroft and Wadge: SIAM Jour. Comp. vol. 5 (1976).)

Define a set $\Gamma$ by

$$\Gamma = \bigcup_{i=0}^{\infty} (\{i\} \times \Gamma) \cup \{\star\}.$$

Define a system

$$L = \{\Gamma\} \cup \{ \{i\} \times X \mid i \in \mathbf{N} \text{ and } X \in L \}.$$

Show that $L$ is effectively given. Show that the elements of $|L|$ can be identified with the finite and infinite sequences of natural numbers. What is the connection between $B$ and $L$?

Show that the combinators of LUCID can be construed as computable mappings of type

$$(L \to T) \to (L \to T)$$

or of type

$$(L \to T) \times (L \to T) \to (L \to T).$$

Conclude that programs in LUCID define computable maps.
