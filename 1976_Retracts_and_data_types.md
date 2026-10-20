# Retracts and data types

Data can be structured in many ways: ordered tuples, lists, arrays, trees, streams, and even operations and functions. The last point becomes clear if one thinks of *parameters*. We would normally hardly consider the pairing function $\lambda x \lambda y.\, \langle x, y \rangle$ as being in itself a piece of data. But if we treat the first variable as a *parameter*, then it can be specialized to a *fixed value*, say the element $a$, producing the function $\lambda y.\, \langle a, y \rangle$. This function is more likely to be the output of some process and *in itself* can be considered as a datum. It is rather like one *whole row* of a matrix. If we were to regard a two-argument function $f$ as being a matrix, then its $a$th row would be exactly $\lambda y.\, f(a)(y)$. If $s$ were a selection function, then, for example, $\lambda y.\, f(s(y))(y)$ would represent the selection of one element out of each column of the matrix. This selection could be taken as a specialization of parameters in the operator $\lambda u \lambda v \lambda y.\, u(v(y))(y)$. We have not been very definite here about the exact nature of the fixed $a$, $f$, or $s$, or the range of the variable $y$ or the range of values of the function $f$. The point is only to recall a few elements of structure and to suggest an abstract view of data going beyond the usual iterated arrays and trees.

What then is a *data type*? Answer: a type of data. That is to say, a collection of data that have been grouped together for reasons of similarity of structure or perhaps mere convenience. Thus the collection may very well be a mixed bag, but more often than not canons of taste or demands of simplicity dictate an adherence to regularity. The grouping may be formed to eliminate irrelevant objects and focus the attention in other ways. It is frequently a matter of good organization that aids the understanding of complex definitions. In programming languages, one of the major reasons for making an explicit declaration of a data type (that is, the restriction of certain variables to certain *"modes"*) is that the computed objects of that type can enjoy a special *representation* in the machine that allows the manipulation of these objects via the chosen representation to be reasonably efficient. This is a very critical matter for good language design and good compiler writing. In this report, however, we cannot discuss the problems of representation, important as they may be. Our objective here is conceptual organization, and we wish to show how such ideas, in the language for computable functions used here, can find the proper expression.

Which are the data types that can be defined in LAMBDA? No final answer can be given since the number is infinite and inexhaustible. From one point of view, however, there is only one: $\mathbf{P}\omega$ itself. It is the universal type and all other types are subtypes of it; so $\mathbf{P}\omega$ plays a primary role in this exposition. But in a way it is too big, or at least too complex, since each of its elements can be used in so many different ways. When we specify a subtype the intention is to restrict attention to a special use. But even the various subtypes overlap, and so the same elements still get different uses. Style in writing definitions will usually make the differentiation clear though. The main innovation to be described in this section is the use of LAMBDA expressions to define types *as well as* elements. Certain expressions define *retracts* (or better: retraction mappings), and it is the *ranges* (or as we shall see: *sets of finite points*) of such retracts that form the groupings into types. Thus LAMBDA provides a calculus of type definitions including *recursive* type definitions. Examples will be explained both here and in the following sections. Note that types as retracts turn out to be types as *lattices*, that is, types of partial and many-valued objects. The problem of cutting these lattice types down to the perfect or complete objects is discussed in § 6. Another view of types and functionality of mappings is presented in § 7.

The notion of a retract comes from (analytic) topology, but it seems almost an accident that the idea can be applied in the present context. The word is employed not because there is some deep tie-up with topology but because it is short and rather descriptive. Three easy examples will motivate the general plan:

$$(4.1) \quad \mathbf{fun} = \lambda u \lambda x.\, u(x);$$

$$(4.2) \quad \mathbf{pair} = \lambda u.\, \langle u_0, u_1 \rangle;$$

$$(4.3) \quad \mathbf{bool} = \lambda u.\, u \sqsupset 0, 1.$$

Here $\sqsupset$ is the *doubly strict conditional* defined by

$$(4.4) \quad z \sqsupset x, y = z \supset (z \supset x, \top), (z \supset \top, y),$$

which has the property that if $z$ is both zero and positive, then it takes the value $\top$ instead of the value $x \cup y$.

**DEFINITION.** An element $a \in \mathbf{P}\omega$ is called a *retract* iff it satisfies the equation $a = a \circ a$.

Of course the $\circ$-notation is used for functional composition in the standard way:

$$(4.5) \quad u \circ v = \lambda x.\, u(v(x)).$$

And it is quite simple to prove that each of the three combinators in (4.1)–(4.3) is a retract according to the definition. But what is the point?

Consider $\mathbf{fun}$. No matter what $u \in \mathbf{P}\omega$ we take, $\mathbf{fun}(u)$ is (the graph of) a *function*. And if $u$ already is (the graph of) a function, then $u = \mathbf{fun}(u)$. That is to say, the range of $\mathbf{fun}$ is the same as the set of fixed points of $\mathbf{fun}$ is the same as the set of all (graphs of) functions. Any mapping $a$ whose range and fixed-point set coincide satisfies $a = a \circ a$, and conversely. A retract is a mapping which “retracts” the whole space onto its range and which is the identity mapping on its range. That is the import of the equation $a = a \circ a$. Strictly speaking, the range is the retract and the mapping is the retraction, but for us the mapping is more important. (Note, however, that distinct retracts can have the same range.) We let the mapping stand in for the range.

Thus the combinator **fun** represents in itself the concept of a *function* (continuous function on $\mathbf{P}\omega$ into $\mathbf{P}\omega$). Similarly **pair** represents the idea of a *pair* and **bool** the idea of being a boolean value as an element of $\{\bot, 0, 1, \top\}$, since we must think in the multiple-valued mode. What is curious (and, as we shall see, useful) is that all these retracts which are defining subspaces are at the same time elements of $\mathbf{P}\omega$.

**DEFINITION.** If $a$ is a retract, we write $u : a$ for $u = a(u)$ and $\lambda u : a.\,\tau$ for $\lambda u.\,\tau[a(u)/u]$.

Since retracts are sets in $\mathbf{P}\omega$, we cannot use the ordinary membership symbol to signify that $u$ belongs to the range of $a$; so we write $u : a$. The other notation with the $\lambda$-operator restricts a function to the range of $a$. For $f$ to be so restricted simply means $f = f \circ a$. For the range of $f$ to be contained in that of the retract $a$ means $f = a \circ f$. These algebraic equations will be found to be quite handy. We are going to have a calculus of retracts and mappings between them involving many operators on retracts yet to be discovered. Before we turn to this calculus, we recall the well-known connection between lattices and fixed points.

**THEOREM 4.1 (The lattice theorem).** The fixed points of any continuous function form a complete lattice (under $\subseteq$); while those of a retract form a continuous lattice.

We note further that by the embedding theorem (Theorem 1.6), it follows that any separable (by which we mean countably-based) continuous lattice is a retract of $\mathbf{P}\omega$; hence, our universal space is indeed rich in retracts. A very odd point is that $a = a \circ a$ is a fixed-point equation itself ($\lambda u.\, u \circ u$ is obviously continuous). Thus the retraction mappings form a complete lattice. Is this a continuous lattice? (Ershov has proved it is not; see the Appendix for a sketch.) A related question is solved positively in the next section. Actually the ordering of retracts under $\subseteq$ does not seem to be all that interesting; a more algebraic ordering is given by:

**DEFINITION.** For retracts $a$ and $b$ we write $a \sqsubseteq b$ for $a = a \circ b = b \circ a$.

The idea here should be clear: $a \sqsubseteq b$ means that $a$ is a retract of $b$. It is easy to prove the:

**THEOREM 4.2 (The partial ordering theorem).** The retracts are partially ordered by $\sqsubseteq$.

There do not seem to be any lattice properties of $\sqsubseteq$ of a general nature. Note, however, that if retracts commute, $a \circ b = b \circ a$, then $a \circ b$ is the greatest lower bound under $\sqsubseteq$ of $a$ and $b$. Also if we have a sequence where both $a_n \sqsubseteq a_{n+1}$ and $a_n \subseteq a_{n+1}$ for all $n \in \omega$, then $\bigcup\{a_n \mid n \in \omega\}$ is the upper bound for the $a_n$ under $\sqsubseteq$, as can easily be argued from the definition by continuity of $\circ$.

Certainly there is no “least” retract under $\sqsubseteq$. One has $\bot = \bot \circ a$ (recall: $\bot = \lambda x.\,\bot$), but not $a \circ \bot = \bot$. This last equation means more simply that $a(\bot) = \bot$; that is, $a$ is *strict*. For retracts strictness is thus equivalent to $\bot \sqsubseteq a$, so we can say that there is a least strict retract. The combinator $\mathbf{I} = \lambda u.\, u$ clearly represents the largest retract (the *whole space*), and it is strict also. In a certain sense strictness can be assumed without loss of generality. For if $a$ is not strict, let

$$b = \lambda x.\, \{n \mid a(x) \neq a(\bot)\}.$$

This function takes values in $\{\bot, \top\}$ and is continuous because $\{x \in \mathbf{P}\omega \mid a(x) \neq a(\bot)\}$ is *open*. Next define:

$$a^* = \lambda u.\, a(u) \cap b(u).$$

This is a strict retract whose range is homeomorphic (and lattice isomorphic) to that of $a$. Note, however, that the mapping from $a$ to $a^*$ is not continuous (or even monotonic).

To have a more uniform notation for retracts we shall often write **nil**, **id**, and **seq** for the combinators $\bot$, $\mathbf{I}$, $\mathbf{\$}$. Two further retracts of interest are

$$(4.6) \quad \mathbf{open} = \lambda u.\, \{m \mid \exists e_n \subseteq e_m.\, n \in u\};$$

$$(4.7) \quad \mathbf{int} = \lambda u.\, u \supset 0,\, \mathbf{int}(u - 1) \supset u,\, u.$$

The range of **open** is lattice isomorphic to the lattice of open subsets of $\mathbf{P}\omega$; definition (4.6) is not a LAMBDA-definition of the retract, but such can be given.

In (4.7) we intend **int** to be the least fixed point of the equation. By induction on the least element of $u$ (if any) one proves that:

$$\mathbf{int}(u) = \begin{cases} \bot & \text{if } u = \bot; \\ u & \text{if } u \in \omega; \\ \top & \text{otherwise.} \end{cases}$$

This retract wipes out the distinctions between multiple values, moving all above the singletons up to $\top$; its range thus has a very simple structure. The retract **int** clearly generalizes **bool**. The range of **fun** is homeomorphic to the space of all continuous functions from $\mathbf{P}\omega$ into $\mathbf{P}\omega$; the range of **pair**, to the space of all ordered pairs; the range of **seq**, to the space of all infinite sequences. A combination like $\lambda u.\, \mathbf{int} \circ \mathbf{seq}(u)$ is a retract whose range is homeomorphic to the space of infinite sequences of elements from the range of **int**.

We now wish to introduce some operators that provide systematic ways of forming new combinations of retracts. There are three principal ones:

$$(4.8) \quad a \circ\to b = \lambda u.\, b \circ u \circ a;$$

$$(4.9) \quad a \otimes b = \lambda u.\, \langle a(u_0), b(u_1) \rangle;$$

$$(4.10) \quad a \oplus b = \lambda u.\, u_0 \supset \langle 0, a(u_1) \rangle,\, \langle 1, b(u_1) \rangle.$$

These equations clearly generalize (4.1)–(4.3). Before we explain our operators, note these three equations which hold for arbitrary $a, b, a', b'$:

$$(4.11) \quad (a \circ\to b) \circ (a' \circ\to b') = (a' \circ a) \circ\to (b \circ b');$$

$$(4.12) \quad (a \otimes b) \circ (a' \otimes b') = (a \circ a') \otimes (b \circ b');$$

$$(4.13) \quad (a \oplus b) \circ (a' \oplus b') = (a \circ a') \oplus (b \circ b').$$

The reversal of order $(a' \circ a)$ on the right-hand side of (4.11) should be remarked.

These equations will be used not only for properties of types (ranges of retracts) but also for the mappings between the types.

**THEOREM 4.3 (The function space theorem).** Suppose $a, b, a', b', c$ are retracts. Then we have:

(i) $a \circ\to b$ is a retract, and it is strict if $b$ is;

(ii) $u : a \circ\to b$ iff $u = \lambda x : a.\, u(x)$ and $\forall x : a.\, u(x) : b$;

(iii) if $a \sqsubseteq a'$ and $b \sqsubseteq b'$, then $a \circ\to b \sqsubseteq a' \circ\to b'$;

(iv) if $f : a \circ\to b$ and $f' : a' \circ\to b'$, then $f \circ\to f' : (b \circ\to a') \circ\to (a \circ\to b')$;

(v) if $f : a \circ\to b$ and $f' : b \circ\to c$, then $f' \circ f : a \circ\to c$.

Parts (i), (iii), (iv), and (v) can be proved using (4.8) and (4.11) in an algebraic (formal) fashion. It is (ii) that tells us what it all means: the range of $a \circ\to b$ consists exactly of those functions which are restricted to (the range of) $a$ and which have values in $b$. So we can read $u : a \circ\to b$ in the normal way: $u$ is a (continuous) mapping from $a$ into $b$. In technical jargon, we can say that the (strict) retracts and continuous functions form a *category*. In fact, it is equivalent to the category of separable continuous lattices and continuous maps. In this context, (iv) shows that $\circ\to$ operates not only on spaces (retracts) but also on maps: it is a functor contravariant in the first argument and covariant in the second. Further categorical properties will emerge.

**THEOREM 4.4 (The product theorem).** Suppose $a, b, a', b'$ are retracts. Then we have:

(i) $a \otimes b$ is a retract, and it is strict if $a$ and $b$ are;

(ii) $u : a \otimes b$ iff $u = (u_0, u_1)$ and $u_0 : a$ and $u_1 : b$;

(iii) if $a \sqsubseteq a'$ and $b \sqsubseteq b'$, then $a \otimes b \sqsubseteq a' \otimes b'$;

(iv) if $f : a \circ\to b$ and $f' : a' \circ\to b'$, then $f \otimes f' : a \otimes a' \circ\to b \otimes b'$.

Again the operator proves to be a functor, but what is stated in Theorem 4.4 is not quite enough for the standard identification of $\otimes$ as the categorical product. For this we need some additional combinators:

$$(4.14) \quad \mathbf{fst} = \lambda u.\, u_0;$$

$$(4.15) \quad \mathbf{snd} = \lambda u.\, u_1;$$

$$(4.16) \quad \mathbf{diag} = \lambda u.\, \langle u, u \rangle.$$

Then we have these properties:

$$(4.17) \quad \mathbf{fst} \circ (a \otimes b) : (a \otimes b) \circ\to a;$$

$$(4.18) \quad \mathbf{snd} \circ (a \otimes b) : (a \otimes b) \circ\to b;$$

$$(4.19) \quad \mathbf{diag} \circ a : a \circ\to a \otimes a;$$

$$(4.20) \quad \mathbf{fst} \circ (f \otimes f') = f \circ \mathbf{fst};$$

$$(4.21) \quad \mathbf{snd} \circ (f \otimes f') = f' \circ \mathbf{snd}.$$

Here $a$ and $b$ are retracts and $f$ and $f'$ are functions. Now suppose $a, b$, and $c$ are retracts and $f : c \circ\to a$ and $g : c \circ\to b$. Let

$$h = (f \otimes g) \circ \mathbf{diag} \circ c.$$

We can readily prove that:

$$h : c \circ\to (a \otimes b),$$

and

$$\mathbf{fst} \circ h = f \quad \text{and} \quad \mathbf{snd} \circ h = g.$$

Furthermore, $h$ is the *unique* such function. It is this uniqueness and existence property of functions into $a \otimes b$ that identifies the construct as a product.

There are important connections between $\circ\to$ and $\otimes$. To state these we require some additional combinators:

$$(4.22) \quad \mathbf{eval} = \lambda u.\, u_0(u_1);$$

$$(4.23) \quad \mathbf{curry} = \lambda u \lambda x \lambda y.\, u(\langle x, y \rangle).$$

If $a$, $b$, and $c$ are retracts, the mapping properties are:

$$(4.24) \quad \mathbf{eval} \circ ((b \circ\to c) \otimes b) : ((b \circ\to c) \otimes b) \circ\to c;$$

$$(4.25) \quad \mathbf{curry} \circ ((a \otimes b) \circ\to c) : ((a \otimes b) \circ\to c) \circ\to (a \circ\to (b \circ\to c)).$$

Suppose next that $f : (a \otimes b) \circ\to c$ and $g : a \circ\to (b \circ\to c)$. We find that

$$\mathbf{eval} \circ (\mathbf{curry}(f) \otimes b) = f$$

and

$$\mathbf{curry}(\mathbf{eval} \circ (g \otimes b)) = g.$$

This shows that our category of retracts is a *Cartesian closed category*, which means roughly that product spaces and function spaces within the category interact harmoniously.

**THEOREM 4.5 (The sum theorem).** Suppose $a$, $b$, $a'$, $b'$ are retracts. Then we have:

(i) $a \oplus b$ is a retract, and it is always strict;

(ii) $u : a \oplus b$ iff $u = \bot$ or $u = \top$ or ($u = \langle 0, u_1 \rangle$ and $u_1 : a$) or ($u = \langle 1, u_1 \rangle$ and $u_1 : b$);

(iii) if $a \sqsubseteq a'$ and $b \sqsubseteq b'$, then $a \oplus b \sqsubseteq a' \oplus b'$;

(iv) if $f : a \circ\to b$ and $f' : a' \circ\to b'$, then $f \oplus f' : a \oplus a' \circ\to b \oplus b'$.

There are several combinators associated with $\oplus$:

$$(4.26) \quad \mathbf{inleft} = \lambda x.\, \langle 0, x \rangle;$$

$$(4.27) \quad \mathbf{inright} = \lambda x.\, \langle 1, x \rangle;$$

$$(4.28) \quad \mathbf{outleft} = \lambda u.\, u_0 \supset u_1,\, \bot;$$

$$(4.29) \quad \mathbf{outright} = \lambda u.\, u_0 \supset \bot,\, u_1;$$

$$(4.30) \quad \mathbf{which} = \lambda u.\, u_0;$$

$$(4.31) \quad \mathbf{out} = \lambda u.\, u_1.$$
(The last two are the same as **fst** and **snd**, but they will be used differently.) We find:

$$(4.32) \quad (a \oplus b) \circ \mathbf{inleft} \circ a : a \circ\to (a \oplus b);$$

$$(4.33) \quad (a \oplus b) \circ \mathbf{inright} \circ b : b \circ\to (a \oplus b);$$

$$(4.34) \quad a \circ \mathbf{outleft} \circ (a \oplus b) : (a \oplus b) \circ\to a;$$

$$(4.35) \quad b \circ \mathbf{outright} \circ (a \oplus b) : (a \oplus b) \circ\to b;$$

$$(4.36) \quad \mathbf{which} \circ (a \oplus b) : (a \oplus b) \circ\to \mathbf{bool};$$

$$(4.37) \quad a \circ \mathbf{out} \circ (a \oplus a) : (a \oplus a) \circ\to a;$$

where $a$ and $b$ are retracts. Most of these facts as they stand are trivial until one sets down the relations between all these maps; but there are too many to put them down here. Note, however, if $a$, $b$, and $c$ are retracts and $f : a \circ\to c$ and $g : b \circ\to c$, then if we let

$$h = c \circ \mathbf{out} \circ (f \oplus g),$$

we have:

$$h : (a \oplus b) \circ\to c,$$

and

$$h \circ \mathbf{inleft} = f \quad \text{and} \quad h \circ \mathbf{inright} = g.$$

But, though $h$ exists, it is not unique. So $a \oplus b$ is not the categorical sum (coproduct). The author does not know a neat categorical characterization of this operator.

There would be no difficulty in extending $\otimes$ and $\oplus$ to more factors by expanding the range of indices from $0, 1$ to $0, 1, \ldots, n-1$. The explicit formulae need not be given; but if we write $a_0 \otimes a_1 \otimes \cdots \otimes a_{n-1}$, we intend this expanded meaning rather than the iterated binary product.

To understand sums and other facts about retracts, consider the least fixed point of this equation:

$$(4.38) \quad \mathbf{tree} = \mathbf{nil} \oplus (\mathbf{tree} \otimes \mathbf{tree}).$$

To be certain that **tree** is a retract, we need a general theorem:

**THEOREM 4.6 (The limit theorem).** *Suppose $F$ is a continuous function that maps retracts to retracts and let $c = \mathbf{Y}(F)$. Then $c$ is also a retract. If in addition $F$ maps strict retracts to strict retracts and is monotone in the sense that $a \sqsubseteq b$ implies $F(a) \sqsubseteq F(b)$ for all (strict) retracts $a$ and $b$, then the range of $c$ is homeomorphic to the inverse limit of the ranges of the strict retracts $F^n(\bot)$ for $n \in \omega$.*

This can be applied to the case of (4.38) where $F = \lambda z.\, \mathbf{nil} \oplus (z \otimes z)$. Thus we can analyze **tree** as an inverse limit. This approach has the great advantage over the earlier method of the author where limits were required in showing that **tree** exists. Here we use **Y** to give existence at once, and then apply Theorems 4.3–4.5 to figure out the nature of the retract.

In Theorem 4.6, the fact that $c$ is a retract can be reasoned as follows: $\bot$ is a retract. Thus each $F^n(\bot)$ is a retract. We compute:

$$c \circ c = \bigcup \{F^n(\bot) \mid n \in \omega\} \circ \bigcup \{F^n(\bot) \mid n \in \omega\}$$

$$= \bigcup \{F^n(\bot) \circ F^n(\bot) \mid n \in \omega\} \quad \text{(Note: same $n$.)}$$

$$= \bigcup \{F^n(\bot) \mid n \in \omega\} = c.$$

In case $F$ is monotone and preserves strictness, then we can argue that each $F^n(\bot) \sqsubseteq c$. The retracts $F^n(\bot)$ are the *projections* of $c$ onto the terms of the limit. Of course $F^n(\bot) \sqsubseteq F^m(\bot)$ if $n \le m$. The $u : c$ can be put into a one-to-one correspondence (homeomorphism, lattice isomorphism) with the infinite sequences $\langle v_0, v_1, \ldots, v_n, \ldots \rangle$, where $v_n : F^n(\bot)$ and $v_n = F^n(\bot)(v_{n+1})$. Indeed $v_n = F^n(\bot)(u)$ and $u = \bigcup \{v_n \mid n \in \omega\}$. This is exactly the inverse limit construction.

Retreating from generalities back to the example of **tree**, we can grant that it exists and is provably a retract. Two things in its range are $\bot$ and $\top$ by Theorem 4.5(ii), but they are not so interesting. Now $\bot : \mathbf{nil}$, so by Theorem 4.5(ii) we have $\langle 0 \rangle = \langle 0, \bot \rangle : \mathbf{tree}$. Let us think of this as *the* atom. What else can we have? If $x, y : \mathbf{tree}$, then $\langle x, y \rangle : \mathbf{tree} \otimes \mathbf{tree}$ and so $\langle 1, \langle x, y \rangle \rangle : \mathbf{tree}$. Thus (the range of) **tree** contains an atom and is closed under a binary operation. Note that the atomic and nonatomic trees are distinguished by **which** and that suitable constructor and destructor functions are definable on **tree**. But the space also contains infinite trees since we can solve for the least fixed point of:

$$t = \langle 1, \langle \langle 0 \rangle, t \rangle \rangle$$

and $t : \mathbf{tree}$. (Why?) And there are many other examples of infinite elements in **tree**.

A point to stress in this construction is that **tree** being LAMBDA-definable is *computable*, and there are many computable functions definable on or to (the range of) **tree**. All the "structural" functions, for example, are computable. These are functions which in other languages would be called **isatom** or **construct** or **node**, and they are all easily LAMBDA-definable. Just as with $\oplus$, $\otimes$, $\circ\to$, they are not explicit in the *notation*, but they are definable nevertheless. In the case of **node**, we could use finite sequences of Boolean values to pick out or name nodes. Thus solve for $\mathbf{name} = \mathbf{nil} \oplus \mathbf{bool} \otimes \mathbf{name}$, and then give a recursive definition of:

$$\mathbf{node} : \mathbf{name} \circ\to (\mathbf{tree} \circ\to \mathbf{tree}).$$

Any combination of retract preserving functors can be used in this game. For example:

$$(4.39) \quad \mathbf{lamb} = \mathbf{int} \oplus (\mathbf{lamb} \circ\to \mathbf{lamb}).$$

This looks innocent, but the range of **lamb** would give a quite different and not unattractive model for the $\lambda$-calculus (plus arithmetic). What we do to investigate this model is to modify LAMBDA slightly by replacing the ternary conditional $z \supset x, y$ by a quaternary one $w \supset x, y, z$; otherwise the syntax of the language remains the same. The semantics, however, is a little more complex.

Let us use $\tau$, $\sigma$, $\rho$, $\theta$ as syntactical variables for expressions in the modified language. The semantics is provided by a function $\mathcal{H}$ that maps the expressions of the language to their values in (the range of) **lamb**. To be completely rigorous we also have to confront the question of free and bound variables. For simplicity let us index the variables of the language by integers, and let us take the variables to be $v_0, v_1, v_2, \dots, v_n, \dots$. We cannot simply evaluate out an expression $\tau$ to its value $\mathcal{H}\llbracket \tau \rrbracket$ until we know the values of the free variables in $\tau$. The values of these variables will be given by an "environment" $t$ which can be construed as a *sequence* of values in **lamb**. We can restrict these environments to the retract:

$$(4.40) \quad \mathbf{env} = \lambda t.\, \mathbf{lamb} \circ \mathbf{seq}(t).$$

When $t : \mathbf{env}$, then $t_n : \mathbf{lamb}$ is the value that the environment gives to the variable $v_n$. We also need to employ a transformation on environments as follows:

$$(4.41) \quad t[x/n] = \lambda m \in \omega.\, \mathbf{eq}(n)(m) \supset x,\, t_m.$$

Here **eq** is the primitive recursive function that is $0$, if $n, m$ are equal, and is $1$, otherwise, for $n, m \in \omega$. The effect of $t[x/n]$ is to replace the $n$th term of the sequence $t$ by the value of $x$, otherwise to leave the rest of the sequence unchanged. To correspond with our use of very simple variables we have selected a simple notion of environment: in the semantics of more general languages it is customary to regard an environment as a function from the set of variables into the domain of denotable values.

The correct way to evaluate a term $\tau$ given an environment $t$ is to find $\mathcal{H}\llbracket \tau \rrbracket(t)$. We use the brackets $\llbracket$ and $\rrbracket$ here simply as an aid to the eye in keeping the syntactical part separated from the rest. The environment enters as a function-argument in the usual way; thus we shall have:

$$(4.42) \quad \mathcal{H}\llbracket \tau \rrbracket : \mathbf{env} \to \mathbf{lamb}.$$

$$(4.43) \quad \begin{aligned}
\mathcal{H}\llbracket v_n \rrbracket(t) &= t_n \\
\mathcal{H}\llbracket 0 \rrbracket(t) &= \mathbf{inleft}(0) \\
\mathcal{H}\llbracket \tau + 1 \rrbracket(t) &= \mathbf{which}(\mathcal{H}\llbracket \tau \rrbracket(t) \supset \mathbf{inleft}(\mathbf{out}(\mathcal{H}\llbracket \tau \rrbracket(t)) + 1),\, \bot) \\
\mathcal{H}\llbracket \tau - 1 \rrbracket(t) &= \mathbf{which}(\mathcal{H}\llbracket \tau \rrbracket(t) \supset \mathbf{inleft}(\mathbf{out}(\mathcal{H}\llbracket \tau \rrbracket(t)) - 1),\, \bot) \\
\mathcal{H}\llbracket \theta \supset \tau, \sigma, \rho \rrbracket(t) &= \mathbf{lamb}(\mathbf{which}(\mathcal{H}\llbracket \theta \rrbracket(t) \supset (\mathbf{out}(\mathcal{H}\llbracket \theta \rrbracket(t)) \supset \mathcal{H}\llbracket \tau \rrbracket(t),\, \mathcal{H}\llbracket \sigma \rrbracket(t)),\, \mathcal{H}\llbracket \rho \rrbracket(t))) \\
\mathcal{H}\llbracket \tau(\sigma) \rrbracket(t) &= \mathbf{which}(\mathcal{H}\llbracket \tau \rrbracket(t) \supset \bot,\, \mathbf{out}(\mathcal{H}\llbracket \tau \rrbracket(t))(\mathcal{H}\llbracket \sigma \rrbracket(t))) \\
\mathcal{H}\llbracket \lambda v_n.\,\tau \rrbracket(t) &= \mathbf{inright}(\lambda x : \mathbf{lamb}.\, \mathcal{H}\llbracket \tau \rrbracket(t[x/n])).
\end{aligned}$$

A good question is: why does $\mathcal{H}$ exist? The answer is: because of the fixed-point theorem.

If we rewrite the semantic equations $\mathcal{H}\llbracket \tau \rrbracket(t) = (\dots)$ in (43) by the equation $\mathcal{H}\llbracket \tau \rrbracket = \lambda t : \mathbf{env}\, (\dots)$, then $\mathcal{H}$ is seen to be a function from expressions to values in **lamb**. As the range of **lamb** is contained in $\mathbf{P}\omega$, we can say more broadly that $\mathcal{H} \in \mathbf{P}\omega^{\mathbf{Exp}}$, where **Exp** is the syntactical set of expressions and the exponential notation designates the set of *all* functions from **Exp** into $\mathbf{P}\omega$. This function set is a complete lattice because $\mathbf{P}\omega$ is. Therefore if we read (4.43) as a definition by cases on **Exp**, then we can find $\mathcal{H}$ as a suitable fixed point in the complete lattice $\mathbf{P}\omega^{\mathbf{Exp}}$. Indeed it is the fixed point of a continuous operator.

Actually we can regard **Exp** as being a subset of $\mathbf{P}\omega$ to avoid dragging in other lattices. What we need is another recursive definition of a data type:

$$(4.44) \quad \mathbf{exp} = \mathbf{int} \oplus \mathbf{nil} \oplus \mathbf{exp} \oplus \mathbf{exp} \oplus (\mathbf{exp} \otimes \mathbf{exp} \otimes \mathbf{exp} \otimes \mathbf{exp})$$
$$\qquad \oplus (\mathbf{exp} \otimes \mathbf{exp}) \oplus (\mathbf{int} \otimes \mathbf{exp}).$$

Note that there are as many summands in (4.44) as there are clauses in (4.43). We can think of **exp** as giving the “abstract” syntax of the language. We use the integers to index the variables and the **nil** element to stand for the individual constant. Read (4.44) as saying that every expression is *either* a variable *or* a constant *or* the successor of an expression *or* the predecessor of an expression *or* the conditional formed from a tuple of expressions *or* the abstraction formed from a pair of a variable and an expression. We do not need in (4.44) to introduce special “symbols” for the successor, application, etc., because the separation by cases given by the $\oplus$ operation is sufficient to make the distinctions. (That is why the syntax is “abstract”.) The point is that for recursive definitions it does not matter how we make the distinctions as long as they can be made. From this new point of view, we could rewrite (4.43) so as to show:

$$(4.45) \quad \mathcal{H} : \mathbf{exp} \to (\mathbf{env} \to \mathbf{lamb}),$$

which is clearly more satisfactory—especially as it is now clear that $\mathcal{H}$ is *computable*. And this is a method that can be generalized to many other languages. The method also shows why it is useful to allow *function spaces* as particular data types.

Another example of this method can be illustrated, if the reader will recall the Gödel numbering of § 3. It will be seen that there are similarities with the **tree** construction: instead of $0$ and $\mathbf{apply}(n)(m)$, **tree** uses $\langle 0 \rangle$ and $\langle 1, \langle x, y \rangle \rangle$. Note, however, that Gödel numbers are *finite* while **tree** has *infinite* objects. But the infinite objects are always *limits* of finite objects, so there *are* connections. (We discuss this again in § 6.) In particular, recursive definitions on Gödel numbers, like that of **val**, have analogues on **tree**. Here is the companion of (3.7):

$$(4.46) \quad \mathbf{vaal} = \lambda x : \mathbf{tree}.\, \mathbf{which}(x) \supset \mathbf{G},\, \mathbf{vaal}(\mathbf{fst}(\mathbf{out}(x)))(\mathbf{vaal}(\mathbf{snd}(\mathbf{out}(x)))).$$

We have $\mathbf{vaal} : \mathbf{tree} \to \mathbf{id}$, where of course (4.46) is taken as defining **vaal** as the least fixed point. This is an example of a computable function between effectively given retracts. The LAMBDA-definable elements of $\mathbf{P}\omega$ are the computable elements in the range of **vaal**.

We have discussed the category of retracts and continuous maps, but if they are all LAMBDA-definable, then they fall within the countable model **RE**. Thus there is *another* category of effectively given retracts and effectively given continuous maps. (Examples: **tree**, **id**, **vaal**, and all those retracts and maps generated by $\oplus$, $\otimes$, and $\circ\to$.) This category seems to deserve the status of a generalized recursion theory; though this is not to say that as yet very much is known about it. In fact, the proper formulation may require an enriched category rather than a restricted one. Thus instead of confining attention to the computable retracts and computable maps, it might be better to use the full category with all maps and to single out the computable ones (also maybe the finite ones) by special predicates. In effect we have avoided any methodological decisions by working in the universal space $\mathbf{P}\omega$ and by *defining* a notion when required—if possible with the aid of LAMBDA. This makes it possible to give all the necessary definitions and to prove the theorems without at first having to worry about axiomatic problems.
