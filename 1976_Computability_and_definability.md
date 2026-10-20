# Computability and definability

The purpose of the first section was to introduce in a simple-minded way the basic notions about the topology of $\mathbf{P}\omega$ and its continuous functions. In this section we wish to present the details of a powerful language for defining *particular* functions—especially computable functions—and initiate the study of the *use* of these functions. This study is then extended in different ways in the following sections.

Before looking at the language, a short discussion of the "meaning" of the elements $x \in \mathbf{P}\omega$ will be helpful from the point of view of motivation. Now in itself $x \in \mathbf{P}\omega$ is a set, but this does not reveal its *meaning*. Actually $x$ has no "fixed" meaning, because it can be *used* in strikingly different ways; we look for meaning here solely in terms of use. Nevertheless it is possible to give some coherent guidelines.

In the first place it is convenient to let the singleton subsets $\{n\} \in \mathbf{P}\omega$ stand for the corresponding integers. In fact, we shall enforce by convention the equation $n = \{n\}$ as a way of simplifying notation. In this way, $\omega \subseteq \mathbf{P}\omega$ as a subset. (Note that our convention conflicts with such set-theoretical equations as $5 = \{0, 1, 2, 3, 4\}$. What we have done is to abandon the usual set-theoretical conventions in favor of a slight redefinition of *set of integers* which produces a more helpful convention for present purposes.) So, if we choose, a singleton "means" a single integer. The next
question is what a "large" set $x \in \mathbf{P}\omega$ could mean. Here is an answer: if we write:

$$x = \{0, 5, 17\} = 0 \cup 5 \cup 17,$$

we are thinking of $x$ as a *multiple integer*. This is especially useful in the case of multiple-valued function where we can write:

$$f(a) = 0 \cup 5 \cup 17.$$

Then "$m \in f(a)$" can be interpreted as "$m$ is one value of $f$ at $a$." Now $a \in \mathbf{P}\omega$, too, and so it is a multiple integer also. This brings us to an important point.

A multiple integer is (often) *more* than just the (random) collection of its elements. From the definition of continuity, $m \in f(a)$ is equivalent to $m \in f(e_n)$ with $e_n \subseteq a$. We may not be able to reduce this to $m \in f(\{n\})$ with $n \in a$ without additional assumptions on $f$. Indeed we shall take advantage of the feature of continuous functions whereby the elements of an argument $a$ can join in *cooperation* in determining $f(a)$. Needless to say, continuity implies that the cooperation cannot extend beyond *finite* configurations, and so we can say that $a$ is the union (or limit) of its finite subsets. However, finitary cooperation will be found to be quite a powerful notion.

Where does this interpretation leave the empty set $\varnothing$? When we write "$f(a) = \varnothing$" we can read this as "$f$ has no value at $a$", or "$f$ is undefined at $a$". In this case $f(a)$ exists (as a set), but it is not "defined" as an integer. Single- (or singleton-) valued functions are "well-defined", but multiple-valued functions are rather "over-defined".

How does this interpretation fit in with monotonicity? In case $a \subseteq b$ and $m \in f(a)$, then we must have $m \in f(b)$. We can read "$a \subseteq b$" as "$b$ is an *improvement of* $a$" or "$b$ is *better-defined than* $a$." The point of monotonicity is that the better we define an argument, the better we define a value. "Better" does not imply "well" (that is, singleton-valuedness), and overdefinedness may well creep in. This is not the fault of the function; it is our fault for not choosing a different function.

As a subspace $\omega \subseteq \mathbf{P}\omega$ is discrete. This implies that arbitrary functions $p : \omega \to \omega$ are continuous. Note that $p : \omega \to \mathbf{P}\omega$ as well, because $\omega \subseteq \mathbf{P}\omega$. By Theorem 1.5 we can extend $p$ continuously to $\bar{p} : \mathbf{P}\omega \to \mathbf{P}\omega$. The formula given produces this function:

$$(2.1) \quad \bar{p}(x) = \begin{cases} \bigcap \{p(n) \mid n \in \omega\} & \text{if } x = \varnothing; \\ p(n) & \text{if } x = n \in \omega; \\ \omega & \text{otherwise.} \end{cases}$$

This is a rather abrupt extension of $p$ (the *maximal extension*); a more gradual, continuous extension (the *minimal extension*) is determined by this equation:

$$(2.2) \quad \hat{p}(x) = \bigcup \{p(n) \mid n \in x\}.$$

The same formulae work for *all* multiple-valued functions $p : \omega \to \mathbf{P}\omega$. Functions like $f = \hat{p}$ are exactly characterized as being those continuous functions $f : \mathbf{P}\omega \to \mathbf{P}\omega$ which in addition are *distributive* in the sense of these equations:

$$f(x \cup y) = f(x) \cup f(y) \quad \text{and} \quad f(\varnothing) = \varnothing.$$

The sets $\varnothing$ and $\omega$ play special roles. When we consider them as elements of $\mathbf{P}\omega$ we shall employ the notation:

$$\bot = \varnothing \quad \text{and} \quad \top = \omega$$

The element $\bot$ is the most "undefined" integer, and $\top$ is the most "overdefined". All others are in between.

One last general point on meaning: suppose $x \in \mathbf{P}\omega$ and $k \in x$. Then $k = (n, m)$ for suitable (uniquely determined) integers $n$ and $m$. That is to say, every element of $x$ can be regarded as an ordered pair; thus, $x$ can be used as a relation. Such an operation as

$$(2.3) \quad x ; y = \{(n, l) \mid \exists m.\, (n, m) \in x,\, (m, l) \in y\}$$

is then a continuous function of two variables that treats both $x$ and $y$ as relations. On the other hand we could define a quite different continuous function such as

$$(2.4) \quad x + y = \{n + m \mid n \in x,\, m \in y\}$$

which treats both $x$ and $y$ arithmetically. The only reason we shall probably never write $(x + y) ; x$ again is that the values of this perfectly well-defined continuous function are, for the most part, quite uninteresting. There is, however, no theoretical reason why we cannot use the same set with several different "meanings" in the same formula. Of course if we do so, it is to be expected that we will show the point of doing this in the special case. We turn now to the definition of the general language for defining all such functions.

The syntax and semantics of the language LAMBDA are set out in Table 2. The syntax is indicated on the left, and the meanings of the combinations are shown on the right as subsets of $\mathbf{P}\omega$. This is the basic language and could have been given (less understandably) in terms of combinators (see Theorem 2.4). It is, however, a very primitive language, and we shall require many definitions before we can see why such functions as in (2.3) and (2.4) are themselves definable.

**TABLE 2**

*The language LAMBDA*

$$0 = \{0\}$$

$$x + 1 = \{n + 1 \mid n \in x\}$$

$$x - 1 = \{n \mid n + 1 \in x\}$$

$$z \supset x, y = \{n \in x \mid 0 \in z\} \cup \{m \in y \mid \exists k.\, k + 1 \in z\}$$

$$u(x) = \{m \mid \exists e_n \subseteq x.\, (n, m) \in u\}$$

$$\lambda x.\, \tau = \{(n, m) \mid m \in \tau[e_n / x]\}$$

The definition has been left somewhat informal in hopes that it will be more understandable. In the above, $\tau$ is any term of the language. LAMBDA is type-free and allows any combination to be made by substitution into the given functions. There is one primitive constant $(0)$; there are two unary functions $(x + 1,\, x - 1)$; there is one binary function $(u(x))$ and one ternary function $(z \supset x, y)$; finally there is one variable binding operator $(\lambda x.\, \tau)$. The first three equations have obvious sense. In the fourth, $z \supset x, y$ is McCarthy's conditional expression (a test for zero). Next $u(x)$ defines *application* ($u$ is treated as a graph and $x$ as a set), and $\lambda x.\, \tau$ is *functional abstraction* (compare the definition of **fun**). In defining $\lambda x.\, \tau$, we use $\tau[e_n/x]$ as a shorthand for evaluating the term $\tau$ when the variable $x$ is given the value $e_n$.

Note that the functions are all multiple-valued. Thus we have such a result as:

$$(2.5) \quad (6 \cup 10) + 1 = 7 \cup 11.$$

The partial character of subtraction has expression as:

$$(2.6) \quad 0 - 1 = \bot.$$

We shall see how to define $+$ and $-$ in LAMBDA later. The conditional could also have been defined by cases:

$$(2.7) \quad z \supset x, y = \begin{cases} \bot & \text{if } z = \bot; \\ x & \text{if } z = 0; \\ y & \text{if } 0 \notin z \neq \bot; \\ x \cup y & \text{if } 0 \in z \neq 0. \end{cases}$$

We say that a LAMBDA-term $\tau$ defines a function of its free variables (at least). Other results depend on this fundamental proposition:

**THEOREM 2.1** (The continuity theorem). *All LAMBDA definable functions are continuous.*

Once that is proved, we can use Theorem 1.2 to establish:

**THEOREM 2.2** (The conversion theorem). *The three basic principles $(\alpha)$, $(\beta)$, $(\xi)$ of $\lambda$-conversion are all valid in the model.*

By "model" here we of course understand the interpretation of the language where the semantics gives terms denotations in $\mathbf{P}\omega$ according to the stated definition. Through this interpretation, more properly speaking, $\mathbf{P}\omega$ becomes a model for the axioms $(\alpha)$, $(\beta)$, $(\xi)$. Two well-known results of the calculus of $\lambda$-conversion allow the reduction of functions of several variables to those of *one*, and the reduction of all the primitives to *combinators* (constants)—all this with the aid of the binary operation of application.

**THEOREM 2.3** (The reduction theorem). *Any continuous function of $k$-variables can be written as*

$$f(x_0, x_1, \cdots, x_{k-1}) = u(x_0)(x_1) \cdots (x_{k-1}),$$

*where $u$ is a suitably chosen element of $\mathbf{P}\omega$.*

**THEOREM 2.4** (The combinator theorem). *The LAMBDA-definable functions* can be generated (*from variables*) by iterated application with the aid of these six constants:

$$\mathbf{0} = 0$$

$$\mathbf{suc} = \lambda x.\, x + 1$$

$$\mathbf{pred} = \lambda x.\, x - 1$$

$$\mathbf{cond} = \lambda x \lambda y \lambda z.\, z \supset x, y$$

$$\mathbf{K} = \lambda x \lambda y.\, x$$

$$\mathbf{S} = \lambda u \lambda v \lambda x.\, u(x)(v(x))$$

But the result that makes all this model building and combinatory logic mathematically interesting concerns the so-called *paradoxical combinator* defined by the equation:

$$(2.8) \quad \mathbf{Y} = \lambda u.\, (\lambda x.\, u(x(x)))(\lambda x.\, u(x(x))).$$

**THEOREM 2.5 (The first recursion theorem).** *If $u$ is the graph of a continuous function $f$, then $\mathbf{Y}(u) = \mathbf{fix}(f)$, the least fixed point of $f$.*

There are two points to note here: the fixed point is LAMBDA-definable if $f$ is; and $\mathbf{Y}$ defines a continuous operator. The word “recursion” is attached to the theorem because fixed points are employed to solve recursion equations. It would not be correct to call the fixed-point theorem (Theorem 1.4) the recursion theorem since it only shows that fixed points exist and not how they are definable in a language. The *second* recursion theorem (in Kleene’s terminology) is related, but it involves Gödel numbers as introduced in § 3.

From this point on we see no need to distinguish continuous functions from elements of $\mathbf{P}\omega$; a continuous function will be *identified* with its graph. Note that $u$ is a graph iff $u = \lambda x.\, u(x)$, which is equivalent to Theorem 1.2 (iii). For this reason (functions are graphs) we propose the name *Graph Model* for this model of the $\lambda$-calculus. (There is more to LAMBDA than just $\lambda$, however.)

The identification of functions with graphs entails that the function space of all continuous functions from $\mathbf{P}\omega$ into $\mathbf{P}\omega$ is to be identified (one-to-one) with the subspace

$$\mathbf{FUN} = \{u \mid u = \lambda x.\, u(x)\} \subseteq \mathbf{P}\omega.$$

The identification is *topological* in that the subspace topology agree with the product topology on the function space. This is the topology of pointwise convergence and is closely connected with the lattice structure on the function space which is also defined pointwise (that is, argumentwise). In the notation of $\lambda$-abstraction we can express this as the extension of the axiom of extensionality called $(\xi^*)$ in Table 1 of the Introduction. The laws in Table 1 are not the only ones valid in the model, however. We may also note such argumentwise distribution
laws as:

$$(2.9) \quad (f \cup g)(x) = f(x) \cup g(x);$$

$$(2.10) \quad (\lambda x.\, \tau) \cup (\lambda x.\, \sigma) = \lambda x.\, (\tau \cup \sigma);$$

$$(2.11) \quad (f \cap g)(x) = f(x) \cap g(x);$$

$$(2.12) \quad (\lambda x.\, \tau) \cap (\lambda x.\, \sigma) = \lambda x.\, (\tau \cap \sigma).$$

In the above $f$ and $g$ must be graphs. It is also true that if $\mathscr{F} \subseteq \mathbf{P}\omega$, then

$$(2.13) \quad \bigcup \{f \mid f \in \mathscr{F}\}(x) = \bigcup \{f(x) \mid f \in \mathscr{F}\},$$

but the same does not hold for $\cap$.

We state now a sequence of minor results which show why some simple functions and constants are LAMBDA-definable.

$$(2.14) \quad \bot = (\lambda x.\, x(x))(\lambda x.\, x(x));$$

$$(2.15) \quad x \cup y = (\lambda z.\, 0) \supset x, y; \quad \text{(Hint: } 0, 1 \in \lambda z.\, 0\text{)}$$

$$(2.16) \quad \top = \mathbf{Y}(\lambda x.\, 0 \cup (x + 1));$$

$$(2.17) \quad x \cap y = \mathbf{Y}(\lambda f \lambda x \lambda y.\, x \supset (y \supset 0, \bot), f(x - 1)(y - 1) + 1)(x)(y).$$

The elements $\bot$ and $\top$ are graphs, by the way, and we can characterize them as the only fixed points of the combinator $\mathbf{K}$:

$$(2.18) \quad a = \lambda x.\, a \quad \text{iff} \quad a = \bot \quad \text{or} \quad a = \top.$$

Next we use the notation $\langle x_0, x_1, \dots, x_{n-1} \rangle$ for the function $\hat{p}$ where $p : \omega \to \mathbf{P}\omega$ is defined by:

$$p(i) = \begin{cases} x_i & \text{if } i < n; \\ \bot & \text{if } i \ge n. \end{cases}$$

$$(2.19) \quad \langle \rangle = \bot$$

$$(2.20) \quad \langle x \rangle = \lambda z.\, z \supset x, \bot$$

$$(2.21) \quad \langle x, y \rangle = \lambda z.\, z \supset x, (z - 1 \supset y, \bot)$$

$$(2.22) \quad \langle x_0, x_1, \dots, x_n \rangle = \lambda z.\, z \supset x_0, \langle x_1, \dots, x_n \rangle(z - 1).$$

Obviously we should formalize the subscript notation so that $u_x = u(x)$; then we find:

$$(2.23) \quad \langle x_0, x_1, \dots, x_n \rangle_i = \begin{cases} x_i & \text{if } i < n; \\ \bot & \text{if } i \ge n. \end{cases}$$

This gives us the method of LAMBDA-defining *finite sequences* (in a quite natural way), and the next step is to consider *infinite sequences*. But these are just the functions $\hat{p}$ where $p : \omega \to \mathbf{P}\omega$ is arbitrary. What we need then is a condition expressible in the language equivalent to saying $u = \hat{p}$ for some $p$. This is the same as

$$u = \lambda x.\, \bigcup \{ u_i \mid i \in x \}.$$
but the $\cup$- and set-notation is not part of LAMBDA. We are forced into a recursive definition:

$$(2.24) \quad \mathbf{\$} = \mathbf{Y}(\lambda s \lambda u \lambda z.\, z \supset u_0,\, s(\lambda t.\, u_{t+1})(z - 1)).$$

This equation generalizes (2.22) and we have:

$$(2.25) \quad \mathbf{\$}(u) = \lambda x.\, \bigcup \{ u_i \mid i \in x \}.$$

Thus the combinator $\mathbf{\$}$ “revalues” an element as a distributive function. This suggests introducing the $\lambda$-notation for such functions by the equation:

$$(2.26) \quad \lambda n \in \omega.\, \tau = \mathbf{\$}(\lambda z.\, \tau[z/n]).$$

With all these conventions LAMBDA-notation becomes very much like ordinary mathematical notation without too much strain.

Suppose that $f$ is any continuous function and $a \in \mathbf{P}\omega$. We can define $p : \omega \to \mathbf{P}\omega$ in the ordinary way by primitive recursion where:

$$p(0) = a;$$

$$p(n + 1) = f(n)(p(n)).$$

The question is: can we give a LAMBDA-definition for $\hat{p}$ (in terms of $f$ and $a$ as constants, say)? The answer is clear, for we can prove:

$$(2.27) \quad \hat{p} = \mathbf{Y}(\lambda u \lambda n \in \omega.\, n \supset a,\, f(n - 1)(u(n - 1))).$$

This already shows that a large part of the definitions of recursion theory can be given in this special language. Of course, simultaneous (primitive) recursions can be transcribed into LAMBDA with the aid of the ordered tuples of (2.22), (2.23) above. But we can go further and connect with partial (and general) recursive functions. We state first a definition.

**DEFINITION.** A continuous function $f$ of $k$-variables is *computable* iff the relationship

$$m \in f(e_{n_0})(e_{n_1}) \cdots (e_{n_{k-1}})$$

is recursively enumerable (r.e.) in the integer variables $m, n_0, n_1, \dots, n_{k-1}$.

If $q$ is a partial recursive function in the usual sense, then we can regard it as a mapping $q : \omega \to \omega \cup \{\bot\}$, where $q(n) = \bot$ means that $q$ is undefined at $n$. Saying that $q$ is partial recursive is just to say that $m \in q(n)$ is r.e. as a relation in $n$ and $m$. It is easy to see that this is in turn equivalent to the recursive enumerability of the relationship $m \in \hat{q}(e_n)$; and so our definition is formally a generalization of the usual one. But it is also intuitively reasonable. To “compute” $y = f(x)$, in the one-variable case, we proceed by enumeration. First we begin the enumeration of all finite subsets $e_n \subseteq x$. For each of these $f$ starts up an enumeration of the set $f(e_n)$; so we sit back and observe which $m \in f(e_n)$ by enumeration. The totality of all such $m$ for all $e_n \subseteq x$ forms in the end the set $y$.

**THEOREM 2.6 (The definability theorem).** *For a $k$-ary continuous function $f$, the following are equivalent:*

*(i) $f$ is computable;*

*(ii) $\lambda x_0 \lambda x_1 \cdots \lambda x_{k-1}.\, f(x_0)(x_1) \cdots (x_{k-1})$ as a set is r.e.;*

*(iii) $\lambda x_0 \lambda x_1 \cdots \lambda x_{k-1}.\, f(x_0)(x_1) \cdots (x_{k-1})$ is LAMBDA-definable.*

As a hint for the proof we may note that the method of (2.27) shows that all primitive recursive functions $p$ have the corresponding $\hat{p}$ LAMBDA-definable. Next we remark that a nonempty r.e. set is the range of a primitive recursive function; but the range of $p$ is $\hat{p}(\top)$, which is clearly LAMBDA-definable. That any LAMBDA-definable set (graph) is r.e. is obvious from the definition of the language itself. More details are given in the Appendix.

We may draw some interesting conclusions from the definability theorem. In the first place, we see that the countable collection $\mathbf{RE} \subseteq \mathbf{P}\omega$ of r.e. sets is closed under application and LAMBDA-definability. Indeed it forms a model for the $\lambda$-calculus (axioms $(\alpha)$, $(\beta)$, and $(\xi^*)$ at least) and it also contains the arithmetical combinators. (Clearly there will be many intermediate submodels.) In the second place, we can see now how very easy it is to interpret $\lambda$-calculus in ordinary arithmetical recursion theory by means of quite elementary operations on r.e. sets. Thus the equivalence of $\lambda$-definability with partial recursiveness seems not to be all that good a piece of evidence for Church's Thesis. In his 1936 paper (a footnote on p. 346) Church says about $\lambda$-definability:

> The fact, however, that two such widely different and (in the opinion of the author) equally natural definitions of effective calculability turn out to be equivalent adds to the strength of the reasons adduced below for believing that they constitute as general a characterization of this notion as is consistent with the usual intuitive understanding of it.

The point never struck the present author as an especially telling one, and the reduction of $\lambda$-calculus to r.e. theory shows that the divergence between the theories is not at all wide. Of course it is a pleasant surprise to see how many complicated things can be defined in pure $\lambda$-calculus (without arithmetical combinators), but this fact cuts the wrong way as evidence for the thesis (we want stronger theories, not weaker ones). Post systems (or even first-order theories) are much better to mention in this connection, since they are obviously more inclusive in giving enumerations than Turing machines or Herbrand–Gödel recursion equations. But the equivalence proofs are all so easy! What one would like to see is a "natural" definition where the equivalence with r.e. is not just a mechanical exercise involving a few tricks of coding.

In the course of the development in this section we have stated many equations which are not found in Table 1, and which involve new combinators. In conclusion we would like to mention an equation about $\mathbf{Y}$ which holds in the model, which can be stated in pure $\lambda$-calculus, and which cannot be proved by ordinary reduction (though we shall not try to justify this last statement here). In order to shorten the calculations, we note from definition (2.8) that $\mathbf{Y}(u) = \mathbf{Y}(\lambda y.\, u(y))$; so by Theorem 2.5 this also equals $u(\mathbf{Y}(u))$.

$$(2.28) \quad \mathbf{Y}(\lambda f \lambda x.\, g(x)(f(x))) = \lambda x.\, \mathbf{Y}(g(x)).$$

Call the left side $f'$ and the right $f''$. Now $f'' = \lambda x.\, g(x)(\mathbf{Y}(g(x))) = \lambda x.\, g(x)(f''(x))$, thus $f' \subseteq f''$, because $f'$ is a least fixed point. On the other hand $f' = \lambda x.\, g(x)(f'(x))$, so $f'(x) = g(x)(f'(x))$. Thus $f''(x) \subseteq f'(x)$, because $f''(x)$ is a least fixed point. As this holds for all $x$, we see that $f'' \subseteq f'$; and so they are equal. There must be many other such equations.
