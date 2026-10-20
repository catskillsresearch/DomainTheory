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

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/dsharpPresentation_X.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/dsharpPresentation_X.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/inSharpMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/inSharpMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/inSharpMap_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/inSharpMap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/inSharpMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/inSharpMap_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/inSharp_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/inSharp_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/proj0Map.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/proj0Map.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/proj0_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/proj0_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/proj0_rel_Vsharp_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/proj0_rel_Vsharp_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/proj0_toElementMap_pairSharp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Combinators77/proj0_toElementMap_pairSharp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ConsistencyPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ConsistencyPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/ComputablePresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/ComputablePresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/IsEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/IsEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/inclShuffle.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/inclShuffle.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/reindexInvolutive.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/reindexInvolutive.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/swapPair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/swapPair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/unitPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/unitPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/unitSys_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition71/unitSys_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDfinJoin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDfinJoin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDfinJoinSucc.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDfinJoinSucc.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDfinJoinZero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDfinJoinZero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmemFinJoin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmemFinJoin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmem_finJoin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmem_finJoin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmem_finJoinZero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmem_finJoinZero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmem_finJoin_iUnion.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDmem_finJoin_iUnion.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDsingleton.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition711/PDsingleton.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/IsComputableElement.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/IsComputableElement.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/IsComputableMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/IsComputableMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/apply_isComputableElement.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/apply_isComputableElement.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/comp_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/comp_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/idMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/idMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/principal_isComputableElement.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition72/principal_isComputableElement.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_empty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_empty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_iff_fin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_iff_fin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_union.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_union.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_upSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_upSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/dagger_isomorphic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/dagger_isomorphic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/dagger_upSet_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/dagger_upSet_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/mem_PDunion.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/mem_PDunion.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/upSet_inter_nonempty_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/upSet_inter_nonempty_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/EffectiveIso.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/EffectiveIso.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/EffectivelyIsomorphic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/EffectivelyIsomorphic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/PN.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/PN.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/PN_consistent.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/PN_consistent.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/PN_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/PN_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/PNpres.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/PNpres.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/mem_nbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/mem_nbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/nbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/nbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/nbhd_injective.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/nbhd_injective.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/nbhd_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/nbhd_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/nbhd_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example78/nbhd_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/CONS.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/CONS.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/InclStructure.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/InclStructure.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/MEET.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/MEET.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_i.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_i.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_ii.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_ii.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_iii.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_iii.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_iv.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/axiom_iv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/meet_iff_interEq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/meet_iff_interEq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/mem_ofPresentation_toNbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/mem_ofPresentation_toNbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/mem_toNbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/mem_toNbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_INCL.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_INCL.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_toNbhd_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_toNbhd_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_toPresentation_INCL.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/ofPresentation_toPresentation_INCL.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconElem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconElem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconElemInv.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconElemInv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconIso.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconIso.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconstruct.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconstruct.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconstruct_isomorphic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/reconstruct_isomorphic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_inter_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_inter_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_subset_inter_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_subset_inter_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_top.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toNbhd_top.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise713/toSystem_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/repred_range_primrec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/repred_range_primrec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/repredu2082_exists_primrec_enum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/repredu2082_exists_primrec_enum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/tFun.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise714/tFun.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/IsComputableMapS.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/IsComputableMapS.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/IsEffectivelyGivenS.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/IsEffectivelyGivenS.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/NeighborhoodSystemu2eIsEffectivelyGivenu2etoS.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/NeighborhoodSystemu2eIsEffectivelyGivenu2etoS.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/ScottPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/ScottPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/eq_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/eq_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/exists_list_fiber.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/exists_list_fiber.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/fiber_iterEnum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/fiber_iterEnum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/inclShuffle.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/inclShuffle.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/incl_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/incl_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/interG.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/interG.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterEnum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterEnum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterEnum_cons_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterEnum_cons_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterEnum_inter_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterEnum_inter_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterEnum_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterEnum_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterIdx_ge.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterIdx_ge.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterInter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterInter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterInter_idx_ge.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterInter_idx_ge.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterInter_idx_lt.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterInter_idx_lt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterSys_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/iterSys_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_left.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_left.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_right.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_right.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_subset_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumEnum_subset_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumInMapu2080_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumInMapu2080_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumInMapu2081_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumInMapu2081_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumInMap₀.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumInMap₀.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumInMap₁.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumInMap₁.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumOutMapu2080_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumOutMapu2080_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumOutMapu2081_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumOutMapu2081_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumOutMap₀.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumOutMap₀.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumOutMap₁.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumOutMap₁.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumPresentation_X.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osumPresentation_X.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_eq_master_of_inj₀master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_eq_master_of_inj₀master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_eq_master_of_inj₁master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_eq_master_of_inj₁master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_isEffectivelyGivenS.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_isEffectivelyGivenS.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_mem_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_mem_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_mem_subset_inj₀.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_mem_subset_inj₀.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_mem_subset_inj₁.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/osum_mem_subset_inj₁.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/primrec_inclShuffle.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/primrec_inclShuffle.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/primrec_interG.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/primrec_interG.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/primrec_iterIdx_proj.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/primrec_iterIdx_proj.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/primrec_swapPair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/primrec_swapPair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/projN_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/projN_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/proper₀_dec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/proper₀_dec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/proper₁_dec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/proper₁_dec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_eq_eff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_eq_eff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_eq_prodNbhd_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_eq_prodNbhd_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_proper.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_proper.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_subset_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashEnum_subset_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashPaired.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashPaired.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashPaired_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashPaired_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashPaired_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashPaired_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashPresentation_X.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashPresentation_X.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProju2080_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProju2080_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProju2081_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProju2081_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProj₀.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProj₀.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProj₀_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProj₀_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProj₁.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProj₁.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProj₁_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smashProj₁_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smash_isEffectivelyGivenS.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/smash_isEffectivelyGivenS.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/swapPair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/swapPair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/toScott.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise715/toScott.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/curryComb_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/curryComb_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/curryComb_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/curryComb_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/curryComb_rel_recDecidable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/curryComb_rel_recDecidable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/curryIso_apply.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/curryIso_apply.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/curryStepCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/curryStepCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/primrec_curryStepCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/primrec_curryStepCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/toApproxMap_principal_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise716/toApproxMap_principal_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharpMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharpMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharpMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharpMap_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharp_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharp_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharp_rel_Vsharp_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharp_rel_Vsharp_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1Map.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1Map.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1Map_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1Map_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1_rel_Vsharp_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1_rel_Vsharp_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1_toElementMap_pairSharp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1_toElementMap_pairSharp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/GRel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/GRel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/embZero_ne_embPair_of_memS.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/embZero_ne_embPair_of_memS.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_complete.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_complete.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_out.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_out.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_pair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_sound.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_sound.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_in.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_in.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_pair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_strict.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_strict.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_cod.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_cod.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_dom.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_dom.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_embPair_inv.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_embPair_inv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_embZero_inv.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_embZero_inv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_gamma_inv.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_gamma_inv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_interRight.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_interRight.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_mono.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_mono.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep_gamma.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep_gamma.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep_leaf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep_leaf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep_node.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep_node.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/listGet_rtbl_gEval.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/listGet_rtbl_gEval.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/pair_le_pair_right.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/pair_le_pair_right.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/pair_lt_pair_left.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/pair_lt_pair_left.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/pair_lt_pair_of_lt_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/pair_lt_pair_of_lt_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/primrec_gStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/primrec_gStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/unpair_snd_snd_fst_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/unpair_snd_snd_fst_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/unpair_snd_snd_snd_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/unpair_snd_snd_snd_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise718.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise718.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PDmem_down.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PDmem_down.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PDmem_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PDmem_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmapComb.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmapComb.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmapComb_toElementMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmapComb_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_comp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_comp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_idMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_idMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_isComputable_Ypd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_isComputable_Ypd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_rel_Ypd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_rel_Ypd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_rel_fin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_rel_fin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/bExists_decodeList_re.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/bExists_decodeList_re.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/comp_witness.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/comp_witness.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/exists_stepFun_forall_PFmap_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/exists_stepFun_forall_PFmap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/gather_witnesses.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/gather_witnesses.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_rel_Ypd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_rel_Ypd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_rel_fin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_rel_fin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papply.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papply.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyEval.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyEval.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyEval_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyEval_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyEval_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyEval_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyEval_rel_Ypd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyEval_rel_Ypd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyEval_step_witness.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/papplyEval_step_witness.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/re_forallG_forallX_existsY.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise721/re_forallG_forallX_existsY.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/InS.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/InS.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_inter_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_inter_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_isPositive.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_isPositive.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_master_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_master_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_master_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_master_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_sub_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/Ssys_sub_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/concat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/concat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/concat_mono.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/concat_mono.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/concat_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/concat_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/concat_singleton.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/concat_singleton.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/emb.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/emb.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/emb_injective.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/emb_injective.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/emb_mul.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/emb_mul.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mem_concat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mem_concat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mem_emb.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mem_emb.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mem_mulElem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mem_mulElem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mem_powerLang.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mem_powerLang.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mulElem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mulElem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mulElem_bot_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mulElem_bot_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mulElem_mono_right.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/mulElem_mono_right.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/powerLang.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/powerLang.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/powerLang_concat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/powerLang_concat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/prependMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/prependMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/prependMap_iterElem_mul_streamArrow_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/prependMap_iterElem_mul_streamArrow_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/prependMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/prependMap_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/repeatWord.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/repeatWord.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/repeatWord_succ.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/repeatWord_succ.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/repeatWord_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/repeatWord_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_containsZero_pow_four.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_containsZero_pow_four.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_le_mul_self.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_le_mul_self.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_mul_self.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_mul_self.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_mul_self_append_true.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_mul_self_append_true.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_mul_self_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_mul_self_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_mul_self_self.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamArrow_mul_self_self.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamElem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamElem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamElemMem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722/streamElemMem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat/catEps.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat/catEps.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat/catEps_accepts.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat/catEps_accepts.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat/catEps_mem_eval_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat/catEps_mem_eval_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat/catEps_mem_u3b5Closure_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Cat/catEps_mem_u3b5Closure_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/SingleState.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/SingleState.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/interDFA_accepts.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/interDFA_accepts.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/inter_eval.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/inter_eval.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/sigmaDFA.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/sigmaDFA.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/sigmaDFA_accepts.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/sigmaDFA_accepts.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/sigmaDFA_accepts_denote.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/sigmaDFA_accepts_denote.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/singleDFA.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/singleDFA.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/singleDFA_accepts.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/singleDFA_accepts.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/singleDFA_accepts_denote.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/singleDFA_accepts_denote.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/singleDFA_evalFrom.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/singleDFA_evalFrom.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/singleDFA_evalFrom_none.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722DFA/singleDFA_evalFrom_none.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/BasicInst40.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/BasicInst40.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/NFAinter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/NFAinter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/NFAinter_mem_accepts_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/NFAinter_mem_accepts_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/NFAinter_mem_eval_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/NFAinter_mem_eval_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/PathSplit.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/PathSplit.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/accepts_card_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/accepts_card_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/accepts_shorten_step.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/accepts_shorten_step.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/accepts_skip_loop.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/accepts_skip_loop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/autState.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/autState.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/autStateCard.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/autStateCard.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/autStateCard_eq_card.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/autStateCard_eq_card.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/autStateCard_le_card.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/autStateCard_le_card.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/consistentB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/consistentB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/consistentB_iff_Ssys.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/consistentB_iff_Ssys.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/decideEmptyB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/decideEmptyB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/decideEmptyB_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/decideEmptyB_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/decideNonemptyB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/decideNonemptyB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/decideNonemptyB_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/decideNonemptyB_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/denote_eq_empty_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/denote_eq_empty_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/denote_nonempty_iff_short.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/denote_nonempty_iff_short.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/dfaToNFA_accepts.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/dfaToNFA_accepts.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/dfaToNFA_eval.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/dfaToNFA_eval.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/exists_accepted_word_short.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/exists_accepted_word_short.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/instDecidableEqAutState.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/instDecidableEqAutState.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/instFintypeAutState.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/instFintypeAutState.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/mem_accepts_of_path.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/mem_accepts_of_path.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/nfa_accepts_nonempty_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/nfa_accepts_nonempty_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/nfa_accepts_nonempty_iff_short.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/nfa_accepts_nonempty_iff_short.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathAppend.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathAppend.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathAppend_take_drop.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathAppend_take_drop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathStateAt.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathStateAt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathStateAtAux.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathStateAtAux.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathStateAt_last.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathStateAt_last.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathStateAt_succ.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathStateAt_succ.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathStateAt_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/pathStateAt_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/toNFA.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/toNFA.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/toNFA_accepts.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Decide/toNFA_accepts.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/acceptFin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/acceptFin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/coe_evalFin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/coe_evalFin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/coe_foldl_stepFin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/coe_foldl_stepFin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/coe_startFin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/coe_startFin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/coe_stepFin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/coe_stepFin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/coe_stepFinSingle.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/coe_stepFinSingle.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/denote_iff_evalFin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/denote_iff_evalFin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/diffNFA.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/diffNFA.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/diffNFA_eval.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/diffNFA_eval.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/diffNFA_evalFrom.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/diffNFA_evalFrom.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/diffNFA_mem_accepts_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/diffNFA_mem_accepts_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/evalFin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/evalFin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/exists_diff_word_short.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/exists_diff_word_short.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/interEqB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/interEqB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/interEqB_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/interEqB_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/startFin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/startFin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/stepFin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/stepFin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/stepFinSingle.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/stepFinSingle.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/subsetB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/subsetB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/subsetB_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Equiv/subsetB_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Presentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Presentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722PresentationInst47.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722PresentationInst47.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/BasicInst16.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/BasicInst16.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/BasicInst17.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/BasicInst17.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/BasicInst7.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/BasicInst7.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/InS_denote_of_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/InS_denote_of_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/InS_exists_denote.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/InS_exists_denote.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/SExpr.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/SExpr.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/containsZero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/containsZero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_cap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_cap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_cat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_cat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_catSigmaSigma.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_catSigmaSigma.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_emptyExpr.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_emptyExpr.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_sigma.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_sigma.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_single.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/denote_single.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/emptyExpr.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/emptyExpr.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/empty_iff_equiv_emptyExpr.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/empty_iff_equiv_emptyExpr.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/inS_eq_range_denote.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/inS_eq_range_denote.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/inS_iff_exists_denote.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/inS_iff_exists_denote.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/interEq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/interEq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/matchesB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/matchesB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/matchesB_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/matchesB_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/mem_concat_iff_split.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/mem_concat_iff_split.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/mem_denote_sigma.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/mem_denote_sigma.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/sexprOfNat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/sexprOfNat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/sexprOfNatFuel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/sexprOfNatFuel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/sexprOfNatFuel_sexprToNat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/sexprOfNatFuel_sexprToNat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/sexprToNat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/sexprToNat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/sigma_ne_containsZero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/sigma_ne_containsZero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/snd_lt_pair_of_pos_fst.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Regular/snd_lt_pair_of_pos_fst.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Words.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Words.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Words/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Words/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Words/anyMatchesB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Words/anyMatchesB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Words/mem_wordsUpTo.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Words/mem_wordsUpTo.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Words/wordsUpTo.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise722Words/wordsUpTo.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/Basic/notation16.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/Basic/notation16.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/GraphIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/GraphIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/GraphIdx_mono.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/GraphIdx_mono.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/bitAt.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/bitAt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/bitAt_swap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/bitAt_swap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/bitsCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/bitsCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/bitsList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/bitsList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/bitsStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/bitsStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/capMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/capMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/capMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/capMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/capMap_rel_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/capMap_rel_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/compl_inter_nbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/compl_inter_nbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/compl_nbhd_plusIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/compl_nbhd_plusIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/compl_nbhd_subset_Fun_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/compl_nbhd_subset_Fun_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/compl_nbhd_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/compl_nbhd_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/compl_subset_compl_of_subset.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/compl_subset_compl_of_subset.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/cupMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/cupMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/cupMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/cupMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/cupMap_rel_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/cupMap_rel_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/decodeList_injective.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/decodeList_injective.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/decodeList_untagList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/decodeList_untagList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/elemSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/elemSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/forall_rel_iff_subset_step.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/forall_rel_iff_subset_step.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/funMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/funMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/funMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/funMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/gMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/gMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/gMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/gMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/gMap_rel_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/gMap_rel_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/graphIdx_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/graphIdx_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/graphMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/graphMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/graphMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/graphMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/graphMap_rel_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/graphMap_rel_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/halfIter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/halfIter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/halfIter_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/halfIter_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_Fun_compl_nbhd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_Fun_compl_nbhd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_Fun_compl_nbhd_iffu27.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_Fun_compl_nbhd_iffu27.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_Fun_compl_nbhd_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_Fun_compl_nbhd_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_GraphIdx_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_GraphIdx_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_bitsCodeList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_bitsCodeList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_compl_nbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_compl_nbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_elemSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_elemSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_sumSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/mem_sumSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/nbhd_subset_iff_compl_subset_compl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/nbhd_subset_iff_compl_subset_compl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/nbhd_subset_iff_myLor_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/nbhd_subset_iff_myLor_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/nextCellStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/nextCellStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/nextCellStep_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/nextCellStep_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/orUpTo.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/orUpTo.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusIdx_testBit.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusIdx_testBit.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusMap_rel_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusMap_rel_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep_iter_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep_iter_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep_unpair11.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep_unpair11.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep_unpair12.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep_unpair12.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep_unpair21.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep_unpair21.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep_unpair22.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/plusStep_unpair22.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_nextCellStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_nextCellStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_num.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_num.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_plusIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_plusIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_plusStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_plusStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_tagCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_tagCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_tagOfBits.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_tagOfBits.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_tagStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_tagStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_tri.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_tri.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_unnum1.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_unnum1.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_unnum2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_unnum2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_unnumPair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_unnumPair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_untagList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_untagList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_untagState.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_untagState.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_untagStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_untagStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_untagVal.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/primrec_untagVal.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/sumSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/sumSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/sumSet_mono.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/sumSet_mono.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tagCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tagCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tagCode_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tagCode_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tagOfBits.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tagOfBits.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tagOfBits_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tagOfBits_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tagStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tagStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tag_eq_foldl_reverse.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tag_eq_foldl_reverse.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tag_eq_foldr.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tag_eq_foldr.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tag_untagList_untagVal.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tag_untagList_untagVal.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tag_untagRef.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/tag_untagRef.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/testBit_imp_mem_Fun_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/testBit_imp_mem_Fun_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/testBit_orUpTo.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/testBit_orUpTo.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/testBit_orUpTo_self.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/testBit_orUpTo_self.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnum1.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnum1.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnum1_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnum1_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnum2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnum2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnum2_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnum2_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnumPair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnumPair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnumPair_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/unnumPair_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagList_bitAt_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagList_bitAt_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagRef.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagRef.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagRef_succ_case.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagRef_succ_case.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagRef_zero_case.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagRef_zero_case.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagState.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagState.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagState_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagState_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep_cont.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep_cont.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep_done.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep_done.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep_halt.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep_halt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep_iter_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep_iter_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep_of_done_iterate.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagStep_of_done_iterate.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagVal.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagVal.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagVal_and_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagVal_and_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagVal_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise723/untagVal_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/BasicInst2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/BasicInst2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Gamma.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Gamma.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Gamma_cases.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Gamma_cases.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/HasMin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/HasMin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/L.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/L.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LFunData.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LFunData.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LTdata.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LTdata.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LTpres.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LTpres.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/L_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/L_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/L_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/L_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/L_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/L_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/L_nestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/L_nestedOrDisjoint.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumConsChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumConsChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumConsCharP.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumConsCharP.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumConsCharP_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumConsCharP_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumConsChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumConsChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumConsChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumConsChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInterEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInterEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInterEqCharP.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInterEqCharP.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInterEqCharP_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInterEqCharP_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInterEqChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInterEqChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInterEqChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInterEqChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInter_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumInter_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumSubsetChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumSubsetChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumSubsetChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/LenumSubsetChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_cons_charP_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_cons_charP_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_cons_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_cons_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_cons_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_cons_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_interEq_charP_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_interEq_charP_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_interEq_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_interEq_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_interEq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_interEq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_subset_char_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_subset_char_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_subset_recDecidable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_subset_recDecidable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_surj.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_surj.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lenum_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lmem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lmem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lpres.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Lpres.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/T_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/T_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_eq_canon.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_eq_canon.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_injOn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_injOn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_interEq_iff'.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_interEq_iff'.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_interEq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_interEq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_inter_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_inter_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_inter_eq_TinterCode'.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_inter_eq_TinterCode'.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_inter_eq_TinterCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_inter_eq_TinterCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_ne_empty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_ne_empty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_surj.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_surj.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_two.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_two.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tenum_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/TeqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/TeqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/TeqChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/TeqChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/TinterCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/TinterCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tpres.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tpres.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tpres_cons_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tpres_cons_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tpres_cons_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tpres_cons_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tpres_interEq_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/Tpres_interEq_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andFn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andFn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andFn_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andFn_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andFn_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andFn_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andFn_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andFn_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andFn_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andFn_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andMap2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andMap2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andT.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/andT.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/bitToNat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/bitToNat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/bitToNat_false.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/bitToNat_false.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/bitToNat_true.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/bitToNat_true.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/buildData.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/buildData.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/buildData_eq_finPrefix.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/buildData_eq_finPrefix.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/buildData_succ.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/buildData_succ.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_empty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_empty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_inter_ne.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_inter_ne.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_subset.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_subset.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_subset_of_subset.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/consSet_subset_of_subset.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/cons_injective.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/cons_injective.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/cons_inl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/cons_inl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/cons_inr.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/cons_inr.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/embStr.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/embStr.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/embStr_injective.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/embStr_injective.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/embStr_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/embStr_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/eq_master_of_master_subset.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/eq_master_of_master_subset.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/exists_cons_prefix_of_prefix_of_length_lt.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/exists_cons_prefix_of_prefix_of_length_lt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/exists_extend_of_not_hasMin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/exists_extend_of_not_hasMin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/exists_finPrefix_subset_of_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/exists_finPrefix_subset_of_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_eq_of_streamElement_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_eq_of_streamElement_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_length.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_length.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_prefix_of_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_prefix_of_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_prefix_succ.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_prefix_succ.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_succ.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_succ.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_take.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_take.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/finPrefix_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/gammaEquivElement.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/gammaEquivElement.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/isPrefixChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/isPrefixChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/isPrefixChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/isPrefixChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/isPrefixChar_eq_zero_or_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/isPrefixChar_eq_zero_or_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/isPrefixChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/isPrefixChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/master_ne_one_T.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/master_ne_one_T.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/master_ne_zero_T.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/master_ne_zero_T.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/mem_consSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/mem_consSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/mem_nbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/mem_nbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/mem_nbhd_finPrefix_toStream.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/mem_nbhd_finPrefix_toStream.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/mulBit_eq_zero_or_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/mulBit_eq_zero_or_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_finPrefix_antitone.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_finPrefix_antitone.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_injective.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_injective.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/nbhd_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notFn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notFn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notFn_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notFn_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notFn_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notFn_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notFn_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notFn_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notFn_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notFn_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notT.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/notT.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/ofPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/ofPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/one_inter_zero_T.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/one_inter_zero_T.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/pointwiseBin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/pointwiseBin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/postcompose.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/postcompose.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/pres.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/pres.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumConsChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumConsChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumConsCharP.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumConsCharP.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumInter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumInter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumInterEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumInterEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumInterEqCharP.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumInterEqCharP.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumSubsetChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_LenumSubsetChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_TeqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_TeqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_TinterCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_TinterCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_isPrefixChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_isPrefixChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_isPrefixChar_swap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/primrec_isPrefixChar_swap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/principal_hasMin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/principal_hasMin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/pwArg.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/pwArg.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/pwFst.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/pwFst.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/pwSnd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/pwSnd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/star.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/star.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/star_ne_cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/star_ne_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/star_not_mem_consSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/star_not_mem_consSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamCons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamCons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamCons_succ.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamCons_succ.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamCons_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamCons_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamElement.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamElement.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamElement_injective.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamElement_injective.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamElement_not_hasMin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/streamElement_not_hasMin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/subset_iff_eq_or_eq_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/subset_iff_eq_or_eq_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/toElement.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/toElement.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/toElement_bijective.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/toElement_bijective.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/toElement_injective.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/toElement_injective.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/toElement_surjective.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/toElement_surjective.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/toStream.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/toStream.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/zero_inter_one_T.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/zero_inter_one_T.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/zero_ne_one_T.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise724/zero_ne_one_T.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Fmap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Fmap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Fmap_comp_Gmap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Fmap_comp_Gmap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Fmap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Fmap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Fmap_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Fmap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Fmap_rel_enum_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Fmap_rel_enum_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Gmap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Gmap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Gmap_comp_Fmap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Gmap_comp_Fmap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Gmap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Gmap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Gmap_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Gmap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Gmap_rel_enum_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Gmap_rel_enum_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/IsPartiallyEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/IsPartiallyEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/NeighborhoodSystemu2ePowerDomain_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/NeighborhoodSystemu2ePowerDomain_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_biUnion_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_biUnion_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_exists_Ypd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_exists_Ypd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_exists_Ypd_aux.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_exists_Ypd_aux.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_upSet_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_upSet_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_upSet_inter_biUnion.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PDmem_upSet_inter_biUnion.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/PowerDomain_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_def.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_def.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/UPX_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_cons_code.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_cons_code.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_def.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_def.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerInterCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerInterCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerfoldl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerfoldl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerstep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_innerstep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_interCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_interCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_interEq_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_interEq_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_isPDmem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_isPDmem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_outerfoldl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_outerfoldl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/Ypd_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/eqCode_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/eqCode_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterCode_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterCode_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterStp_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/innerInterStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/interCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/interCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/interCode_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/interCode_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/mem_UPX.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/mem_UPX.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/mem_Ypd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/mem_Ypd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/outerInterStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/outerInterStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/outerInterStp_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/outerInterStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_innerInterStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_innerInterStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_interCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_interCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_outerInterStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/primrec_outerInterStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/subCode_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/subCode_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSetUnion_cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSetUnion_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSetUnion_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSetUnion_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSet_inter_eq_empty_of_not_cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSet_inter_eq_empty_of_not_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSet_subset_Ypd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition710/upSet_subset_Ypd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/HasTop.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/HasTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDext.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDext.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_rel_PD.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_rel_PD.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_rel_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_rel_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_toElementMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMap₂.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMap₂.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoin_inter_two.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoin_inter_two.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoin_pair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoin_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_rel_Ypd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_rel_Ypd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonMeet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonMeet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonMeet_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonMeet_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingleton_mono.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingleton_mono.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingleton_principal.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingleton_principal.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_mem_false.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_mem_false.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_mem_true.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_mem_true.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_not_hasTop.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_not_hasTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_not_mem_empty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_not_mem_empty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/ext_of_principal.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/ext_of_principal.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod_toElementMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/ft_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/ft_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_inter_closed.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_inter_closed.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_iso.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_iso.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_trianglelefteq_powerDomain.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_trianglelefteq_powerDomain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/improperTop.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/improperTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/powerDomain_hasTop.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/powerDomain_hasTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/singleton_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/singleton_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/subsystem_inter_closed.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/subsystem_inter_closed.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/tf_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/tf_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/vshape_not_trianglelefteq_powerDomain.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/vshape_not_trianglelefteq_powerDomain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_eq_Gamma_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_eq_Gamma_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_even.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_even.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_even_inter_even.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_even_inter_even.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_even_inter_odd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_even_inter_odd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_inter_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_inter_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_odd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_odd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_odd_inter_even.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_odd_inter_even.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_odd_inter_odd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_odd_inter_odd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_succ.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_succ.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_surj.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_surj.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_zero_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_zero_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/consB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/consB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/consB_packT.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/consB_packT.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_i0.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_i0.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_j0.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_j0.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_ll.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_ll.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_ln.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_ln.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_nl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_nl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_nn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_nn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_decider_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_decider_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_intI_correct.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_intI_correct.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_interEq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_interEq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/eqB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/eqB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/eqB_packT.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/eqB_packT.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/exists_sub_embPair_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/exists_sub_embPair_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/exists_sub_embZero_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/exists_sub_embZero_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gList_length.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gList_length.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gOf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gOf_def.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gOf_def.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/getD_gList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/getD_gList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/intI.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/intI.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/intI_packT.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/intI_packT.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/le_pair_left.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/le_pair_left.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGetStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGetStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGetStp_pair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGetStp_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_encodeList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_encodeList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_foldl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_foldl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_foldl_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_foldl_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_rtbl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_rtbl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/max_sq_le_pair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/max_sq_le_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/memS_sub_embPair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/memS_sub_embPair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/memS_sub_embZero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/memS_sub_embZero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/nat_shape.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/nat_shape.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/packT.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/packT.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/pair_lt_pair_of_lt.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/pair_lt_pair_of_lt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/pair_lt_succ_sq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/pair_lt_succ_sq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_dsharpStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_dsharpStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_gOf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_gOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_listGet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_listGet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_listGet₂.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_listGet₂.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_rtbl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_rtbl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/rtbl.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/rtbl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/rtbl_eq_encode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/rtbl_eq_encode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/rtbl_eq_rec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/rtbl_eq_rec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/unpair_fst_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/unpair_fst_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/REPred.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/REPred.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/REPredu2eforall_mem_decodeListu2082.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/REPredu2eforall_mem_decodeListu2082.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/REPred₂.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/REPred₂.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2082u2ebExistsList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2082u2ebExistsList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2082u2ebForallList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2082u2ebForallList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2082u2eof_paired_zero_one_char.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2082u2eof_paired_zero_one_char.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2082u2eswap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2082u2eswap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2083u2eof_triple_zero_one_char.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2083u2eof_triple_zero_one_char.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2ebExists.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2ebExists.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2ebForall.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2ebForall.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2eof_zero_one_char.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidableu2eof_zero_one_char.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidable₂.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidable₂.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidable₃.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/RecDecidable₃.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/allBinDigitsChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/allBinDigitsChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/allListChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/allListChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/allListStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/allListStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/amGM.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/amGM.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/appendListCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/appendListCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/appendListCode_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/appendListCode_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/appendListTabFn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/appendListTabFn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/autStateCardFuelChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/autStateCardFuelChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/autStateCardFuelCharBody.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/autStateCardFuelCharBody.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/autStateCardFuelCharLookup.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/autStateCardFuelCharLookup.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/autStateCardFuelChar_fuelTable_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/autStateCardFuelChar_fuelTable_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/bExistsFn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/bExistsFn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/bForallFn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/bForallFn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/c9b5_boolNat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/c9b5_boolNat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/c9b5_encodeListBool.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/c9b5_encodeListBool.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/c9b5_sexprDepth.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/c9b5_sexprDepth.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/c9b5_sexprGodelEncode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/c9b5_sexprGodelEncode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/c9b6_decodeListBool.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/c9b6_decodeListBool.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/capCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/capCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/codeBound.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/codeBound.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/codeBound_succ.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/codeBound_succ.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/codeBound_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/codeBound_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/consistentBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/consistentBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/consistentBChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/consistentBChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/consistentBChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/consistentBChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decideNonemptyBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decideNonemptyBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decideNonemptyBChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decideNonemptyBChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeFuelOkChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeFuelOkChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeFuelOkCharBody.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeFuelOkCharBody.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeFuelOkCharLookup.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeFuelOkCharLookup.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeFuelOkChar_fuelTable_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeFuelOkChar_fuelTable_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeFuelOkChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeFuelOkChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeList_foldl_mapPairStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeList_foldl_mapPairStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeList_length_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeList_length_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeList_mapPairCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeList_mapPairCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeList_mapPairStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/decodeList_mapPairStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/dropCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/dropCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/dropListTabFn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/dropListTabFn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/encodeList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/encodeList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/eqZero_bit.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/eqZero_bit.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/eq_of_le_one_iff_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/eq_of_le_one_iff_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListChar_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListChar_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListStp_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsListStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsList_foldl_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/existsList_foldl_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/foldCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/foldCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/foldStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/foldStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTableStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTableStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTableStep_nth.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTableStep_nth.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTable_eq_of_recursion.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTable_eq_of_recursion.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTable_succ_nth.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTable_succ_nth.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTable_zero_nth.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/fuelTable_zero_nth.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/geTwo_bit.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/geTwo_bit.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/getD_append_cf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/getD_append_cf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/getD_append_right_cf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/getD_append_right_cf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/halfParity.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/halfParity.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/halfParity_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/halfParity_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/interEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/interEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/interEqChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/interEqChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/interEqChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/interEqChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isBinDigit.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isBinDigit.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isOne.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isOne.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isOne_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isOne_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isOne_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isOne_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isOne_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isOne_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isZero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/isZero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/iter_sq_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/iter_sq_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/le_pair_right.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/le_pair_right.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listEqStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listEqStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listEqStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listEqStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listEqStpNonzero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listEqStpNonzero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listLenChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listLenChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listLenStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/listLenStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/lorStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/lorStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/lowOr.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/lowOr.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/lt_iter_succ_sq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/lt_iter_succ_sq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/lt_of_mul_lt_mul_left'.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/lt_of_mul_lt_mul_left'.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/lt_succ_sqrt.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/lt_succ_sqrt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/mapPairCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/mapPairCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/mapPairStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/mapPairStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/mapPairStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/mapPairStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/mapPairStp_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/mapPairStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBCatG.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBCatG.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBCatGLookup.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBCatGLookup.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBCharBody.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBCharBody.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBCharBodyLookup.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBCharBodyLookup.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBChar_fuelTable_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/matchesBChar_fuelTable_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/mulBit.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/mulBit.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/myLor.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/myLor.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/natEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/natEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/natEqChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/natEqChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/nthCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/nthCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/nthStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/nthStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/pair_unpair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/pair_unpair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_allListChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_allListChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_appendListCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_appendListCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_appendListTabFn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_appendListTabFn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_autStateCardFuelChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_autStateCardFuelChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_autStateCardFuelChar2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_autStateCardFuelChar2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_autStateCardFuelCharLookup.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_autStateCardFuelCharLookup.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_bForallFn_param.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_bForallFn_param.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_codeBound.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_codeBound.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_consistentBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_consistentBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_consistentBChar2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_consistentBChar2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_decideNonemptyBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_decideNonemptyBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_decideNonemptyBChar2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_decideNonemptyBChar2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_decodeFuelOkChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_decodeFuelOkChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_decodeFuelOkChar2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_decodeFuelOkChar2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_decodeFuelOkCharLookup.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_decodeFuelOkCharLookup.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_div2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_div2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_existsListChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_existsListChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_existsListStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_existsListStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_fuelTable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_fuelTable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_halfParity.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_halfParity.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_interEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_interEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_ite.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_ite.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_lorStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_lorStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_lowOr.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_lowOr.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_mapPairCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_mapPairCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_mapPairStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_mapPairStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_matchesBCatGLookup.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_matchesBCatGLookup.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_matchesBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_matchesBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_matchesBChar2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_matchesBChar2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_matchesBCharBodyLookup.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_matchesBCharBodyLookup.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_max.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_max.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_max_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_max_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_mod2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_mod2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_myLor.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_myLor.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_pow.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_pow.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_powu2082.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_powu2082.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_subsetBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_subsetBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_two_pow.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/primrec_two_pow.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/reForallChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/reForallChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/reForallF.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/reForallF.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/reForallStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/reForallStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/rePred_of_forall.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/rePred_of_forall.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/recDecidable_of_forall.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/recDecidable_of_forall.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/recDecidableu2082_of_forall.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/recDecidableu2082_of_forall.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/recPow_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/recPow_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/selectFn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/selectFn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/selectFn_isOne_one_sub_sigma.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/selectFn_isOne_one_sub_sigma.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/selectFn_ite.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/selectFn_ite.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/selectFn_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/selectFn_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/selectFn_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/selectFn_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/sqrt_add_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/sqrt_add_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/sqrt_eq_of.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/sqrt_eq_of.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/sqrt_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/sqrt_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/sqrt_le_add.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/sqrt_le_add.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/subsetBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/subsetBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/subsetBChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/subsetBChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/subsetBoundChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/subsetBoundChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/subsetGuardChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/subsetGuardChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/tabCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/tabCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/tabStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/tabStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/takeCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/takeCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/takeListTabFn.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/takeListTabFn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/unpair_pair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/unpair_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/unpair_pair_fst.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/unpair_pair_fst.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/unpair_pair_snd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/unpair_pair_snd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/unpair_snd_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Recursive/unpair_snd_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysPres.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysPres.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysX.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysX.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysX_default.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysX_default.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysX_eq_denote_safe.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysX_eq_denote_safe.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysX_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysX_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysX_surj.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/SsysX_surj.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Ssys_cons_computable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Ssys_cons_computable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Ssys_cons_computable_of_primrec_ssysConsChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Ssys_cons_computable_of_primrec_ssysConsChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/eqSEdec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/eqSEdec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_eq_inj₁_elim.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_eq_inj₁_elim.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_ne_inj₁_of_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_ne_inj₁_of_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_ne_sumMaster.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_ne_sumMaster.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₁_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₁_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₁_ne_sumMaster.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₁_ne_sumMaster.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/paired_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/paired_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodEnum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodEnum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodEnum_apply.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodEnum_apply.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodNbhd_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodNbhd_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodPresentation_X.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodPresentation_X.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prod_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prod_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/proju2080_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/proju2080_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/proju2081_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/proju2081_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/recDec_setEq₀.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/recDec_setEq₀.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/recDec_setEq₁.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/recDec_setEq₁.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_eq_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_inter_sumMaster.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_inter_sumMaster.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_subset_sumMaster.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_subset_sumMaster.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_zero.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumMaster_inter_sumEnum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumMaster_inter_sumEnum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/tag_trichotomy.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/tag_trichotomy.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_inter_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_inter_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_isComputableElement_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_isComputableElement_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_neg.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_neg.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_pos.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_pos.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_singleton.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/Xenum_singleton.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/andFoldl_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/andFoldl_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/andFoldl_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/andFoldl_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStp_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/appendStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/bitSelect.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/bitSelect.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/bitSelect_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/bitSelect_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/botMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/botMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/botMap_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/botMap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condFoldl_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condFoldl_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_cons_neg.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_cons_neg.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_cons_pos.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_cons_pos.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_eq_interYs.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_eq_interYs.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_subset.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/condSet_subset.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consChain_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consChain_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consCharAt.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consCharAt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consPairChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consPairChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consPairChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consPairChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consUpd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/consUpd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/curry_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/curry_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/curry_rel_Xenum_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/curry_rel_Xenum_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_appendCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_appendStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_appendStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_encodeList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_encodeList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_foldl_appendStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/decodeList_foldl_appendStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/eqEnumChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/eqEnumChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/eqEnumChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/eqEnumChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/evalMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/evalMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/evalMap_rel_prodNbhd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/evalMap_rel_prodNbhd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/exists_funListOf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/exists_funListOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funConsChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funConsChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funImpChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funImpChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_append.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_append.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_cons.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_cons.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_valid.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funListOf_valid.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair_fst.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair_fst.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair_snd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPair_snd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/funPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/idxchain.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/idxchain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interEqChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interEqChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interFrom.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interFrom.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList_nil.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList_nil.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList_subset_base.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interList_subset_base.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsIdx_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsIdx_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYsStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYs_funList_mem_of_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/interYs_funList_mem_of_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/isComputableElement_funPresentation_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/isComputableElement_funPresentation_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_Xenum_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_Xenum_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_Xenum_iff_map.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_Xenum_iff_map.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_condSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/mem_condSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_appendCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_consPairChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_consPairChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_eqEnumChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_eqEnumChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interYsIdx.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interYsIdx.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interYsStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_interYsStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_subChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_subChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_subStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_subStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_trivStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_trivStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_trivialChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/primrec_trivialChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/rel_interYs_funList.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/rel_interYs_funList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/selectFn_isOne.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/selectFn_isOne.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/selectFn_mul_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/selectFn_mul_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_appendCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_appendCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_eq_univ_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_eq_univ_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/stepFun_funListOf_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/subStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivialChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivialChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivialChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem75/trivialChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/Xenum_codePair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/Xenum_codePair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/chainDec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/chainDec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/chainDec_iff_gStepsOK.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/chainDec_iff_gStepsOK.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/codePair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/codePair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixElement_mem_iff_chain.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixElement_mem_iff_chain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixMap_rel_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixMap_rel_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep_foldl_fst.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep_foldl_fst.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep_foldl_snd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep_foldl_snd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixStp_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gLastOf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gLastOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK_complete.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK_complete.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK_sound.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK_sound.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/leastMap_Xenum_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/leastMap_Xenum_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/primrec_fixChainChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/primrec_fixChainChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/primrec_fixStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/primrec_fixStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/boolNat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/boolNat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/boolNat_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/boolNat_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/boolNat_zero_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/boolNat_zero_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/c9b5_encodeListBool_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/c9b5_encodeListBool_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/c9b5_sexprDepth_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/c9b5_sexprDepth_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/c9b5_sexprGodelEncode_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/c9b5_sexprGodelEncode_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/consistentB_safe_sigma.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/consistentB_safe_sigma.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/consistentB_sigma_safe.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/consistentB_sigma_safe.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuelOkChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuelOkChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_depth_le.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_depth_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_encode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_encode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_pair_cap_isSome_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_pair_cap_isSome_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_pair_cat_isSome_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_pair_cat_isSome_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_sound.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_sound.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_cap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_cap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_cat.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_cat.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_junk.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_junk.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_not_sigma.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_not_sigma.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_sigma.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_sigma.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_single.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeFuel_succ_single.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeListBool.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeListBool.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeListBool_encodeListBool.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeListBool_encodeListBool.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeListBool_eq_some.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeListBool_eq_some.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeListBool_isSome_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decodeListBool_isSome_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decode_index.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/decode_index.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/encode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/encode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/encodeListBool.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/encodeListBool.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/exists_inner_bound.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/exists_inner_bound.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2_iterEnum_iter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2_iterEnum_iter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2_mono.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2_mono.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2_reindexF.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber2_reindexF.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber_reindexG.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/fiber_reindexG.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/index.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/index.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/iterIterEffectiveIso.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/iterIterEffectiveIso.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/mapM_natBool_eq_some.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/mapM_natBool_eq_some.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/mapM_natBool_isSome_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/mapM_natBool_isSome_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/masterIdx_iterPresentation.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/masterIdx_iterPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/mem_fiber2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/mem_fiber2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/mem_fiber2_of_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/mem_fiber2_of_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/natBinDigit_of_natBool_some.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/natBinDigit_of_natBool_some.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/natBool.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/natBool.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/natBool_eq_some_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/natBool_eq_some_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/natBool_isSome_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/natBool_isSome_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/pair_lt_pair_of_lt.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/pair_lt_pair_of_lt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/primrec_ssysActiveChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/primrec_ssysActiveChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/primrec_ssysConsChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/primrec_ssysConsChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/primrec_ssysConsistentBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/primrec_ssysConsistentBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexF.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexF.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexF_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexF_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexF_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexF_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexG.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexG.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexG_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexG_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexG_subset_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/reindexG_subset_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/safeDecodeActive.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/safeDecodeActive.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/safeDecodeActive_inactive.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/safeDecodeActive_inactive.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/safeDecodeActive_nonempty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/safeDecodeActive_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/sexprDepth.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/sexprDepth.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysActive.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysActive.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysActiveChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysActiveChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysActiveChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysActiveChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysActiveChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysActiveChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysActive_exists_decode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysActive_exists_decode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysCanonicalCode.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysCanonicalCode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsChar_eq_ssysConsistentBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsChar_eq_ssysConsistentBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsChar_zero_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsChar_zero_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsistentB.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsistentB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsistentBChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsistentBChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsistentBChar_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsistentBChar_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsistentBChar_le_one.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsistentBChar_le_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsistentB_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysConsistentB_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysInterEqChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssysInterEqChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssys_cons_char_eq_one_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssys_cons_char_eq_one_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssys_cons_char_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssys_cons_char_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssys_cons_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssys_cons_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssys_cons_positivity.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssys_cons_positivity.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssys_inter_nonempty_iff_consistent.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/ssys_inter_nonempty_iff_consistent.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/toDomainIso.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/toDomainIso.lean)
