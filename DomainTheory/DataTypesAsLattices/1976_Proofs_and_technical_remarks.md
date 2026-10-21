# Appendix A. Proofs and technical remarks

**For Section 1.** If we give the two-point space $\{\bot, \top\}$ the weak $T_0$-topology with just three open sets: $\varnothing$, $\{\top\}$, $\{\bot, \top\}$, we have what is called the Sierpinski space; and its infinite product $\{\bot, \top\}^\omega$ with the product topology is the same as $\mathbf{P}\omega$. The finite sets $e_n \in \mathbf{P}\omega$ correspond exactly to the usual basic open sets for the product. For those familiar with such notions, this well-known observation makes many of the facts mentioned in this section fairly obvious. From any point of view, Theorem 1.1 and the remarks in the following paragraph are simple exercises.

*Proof of Theorem 1.2.* Equation (i) as a functional equation comes down to

$$\{m \mid \exists e_n \subseteq x.\; m \in f(e_n)\} = f(x),$$

which is just another way of writing the definition of continuity. Thus it is indeed true for all $x$. Next, inclusion (ii) means that if $(n, m) \in u$, then $\exists e_k \subseteq e_n.\; (k, m) \in u$. Clearly all we need to do is take $k = n$. If we also want the converse inclusion to hold, then what we need is condition (iii).

*Proof of Theorem 1.3.* Substitution is generalized composition of functions of many variables with all possible identifications and permutations of the variables; however, as we are able to define continuity by separating the variables, the argument reduces to a few special cases. The first trick is to take advantage of monotonicity. Thus, suppose $f(x, y)$ is continuous in each of its variables. What can we say of $f(x, x)$, a very special case of substitution? We calculate

$$f(x, x) = \bigcup \{f(e_n, x) \mid e_n \subseteq x\}$$

$$= \bigcup \{f(e_n, e_m) \mid e_n \subseteq x,\; e_m \subseteq x\}.$$

Then if we think of $e_k = e_n \cup e_m$ and realize that $f(e_n, e_m) \subseteq f(e_k, e_k)$, we see that

$$f(x, x) = \bigcup \{f(e_k, e_k) \mid e_k \subseteq x\}.$$

This means that $f(x, x)$ is continuous in $x$. This same argument works if other variables are present, as in the passage from $f(x, y, z, w)$ to $f(x, x, z, w)$. When an identification of more than two variables is required, as from $f(x, y, z, w)$ to $f(x, x, x, x)$, the principle is just applied several times.

Finally, to show that $f(g(x, y), h(y, x, y))$ is continuous, it is sufficient to show that $f(g(x, y), h(z, u, v))$ is continuous in each of its variables separately. By simply overlooking the remaining variables, this comes down to showing that $f(g(x))$ is continuous if $f$ and $g$ are. But the proof for ordinary composition is very easy with the aid of the characterization theorem (Theorem 1.1).

*Proof of Theorem 1.4.* This well-known fact holds for continuous functions on many kinds of chain-complete partial orderings; but $\mathbf{P}\omega$ illustrates the idea well enough. Suppose $f$ had a fixed point $x = f(x)$. Then since $\varnothing \subseteq x$ and $f$ is monotonic, we see that $f(\varnothing) \subseteq f(x) = x$. But then again, $f(f(\varnothing)) \subseteq f(x) = x$; and so by induction, $f^n(\varnothing) \subseteq x$. This proves that $\mathbf{fix}(f) \subseteq x$; and thus if $\mathbf{fix}(f)$ is a fixed point, it must be the least one. To prove that it is a fixed point, we need a fact that will often be useful:

**LEMMA.** *If $x_n \subseteq x_{n+1}$ for all $n$, and if $f$ is continuous, then*

$$f\!\left(\bigcup \{x_n \mid n \in \omega\}\right) = \bigcup \{f(x_n) \mid n \in \omega\}.$$

*Proof.* By monotonicity, the inclusion holds in one direction. Suppose $e_m \subseteq f(\bigcup \{x_n \mid n \in \omega\})$. Then by Theorem 1.1 we have $e_m \subseteq f(e_k)$ for some $e_k \subseteq \bigcup \{x_n \mid n \in \omega\}$. Because $e_k$ is finite and the sequence is increasing, we can argue that $e_k \subseteq x_n$ for some $n$. But then $f(e_k) \subseteq f(x_n)$. This shows that $e_m \subseteq \bigcup \{f(x_n) \mid n \in \omega\}$ and proves the inclusion in the other direction. (*Exercise:* Does this property characterize continuous functions?)

*Proof of Theorem 1.4 concluded.* Noting that $f^n(\varnothing) \subseteq f^{n+1}(\varnothing)$ holds for all $n$, we can calculate:

$$f(\mathbf{fix}(f)) = \bigcup \{f(f^n(\varnothing)) \mid n \in \omega\} = \bigcup \{f^{n+1}(\varnothing) \mid n \in \omega\}.$$

But this is just $\mathbf{fix}(f)$, since the only term left out is $f^0(\varnothing) = \varnothing$.

*Proof of Theorem 1.5.* The function $\bar{f}$ is clearly well-defined even when $y \in Y$ has a neighborhood $U$ where $X \cap U = \varnothing$: in that case $\bar{f}(y) = \omega$ by convention on the meaning of $\bigcap$ in $\mathbf{P}\omega$. In case $x \in X$, it is obvious that $\bar{f}(x) \subseteq f(x)$. For the opposite inclusion, suppose that $m \in f(x)$. Because $f$ is continuous and $\{z \mid m \in z\}$ is open in $\mathbf{P}\omega$, there is an open subset $V$ of $X$ such that $x' \in V$ always implies that $m \in f(x')$. But $X$ is a subspace of $Y$, so $V = X \cap U$ for some open subset $U$ of $Y$. Thus we can see why $m \in \bar{f}(x)$. It remains to show that $\bar{f}$ is itself continuous.

We must show that the inverse image under $\bar{f}$ of every open subset of $\mathbf{P}\omega$ is open in $Y$. But the open subsets of $\mathbf{P}\omega$ are unions of finite intersections of sets of the form $\{z \mid m \in z\}$. Thus it is enough to show that $\{y \mid m \in \bar{f}(y)\}$ is always open in $Y$. But this set equals $\bigcup \{U \mid m \in \bigcap \{f(x) \mid x \in X \cap U\}\}$, which being a union of open sets is open. Note that what we have proved is that $\bar{f}$ is continuous no matter what function $f$ is given; however, if $f$ is not continuous, then $\bar{f}$ cannot be an extension of $f$.

For readers not as familiar with general topology we note that the idea of Theorem 1.5 can be turned into a *definition*. Suppose $X \subseteq \mathbf{P}\omega$ is a subset of $\mathbf{P}\omega$. It becomes a subspace with the relative topology. What are the continuous functions $f : X \to \mathbf{P}\omega$? From Theorem 1.5 we see that a necessary and sufficient condition is that $\bar{f} : \mathbf{P}\omega \to \mathbf{P}\omega$ be an extension of $f$. Thus for $x \in X$ we can write the equation $f(x) = \bar{f}(x)$ as a biconditional:

$$m \in f(x) \quad \text{iff} \quad \exists e_n \subseteq x\;\forall x' \in X\; [e_n \subseteq x' \text{ implies } m \in f(x')],$$

which is to hold for all $m \in \omega$. This form of the definition of continuity on a subspace is more complicated than the original definition, because in general $e_n \notin X$ and we cannot write $f(e_n)$.

*Proof of Theorem 1.6.* What $T_0$ means is that every point of $X$ is uniquely determined by its neighborhoods. Now $\varepsilon(x)$ just tells you the set of indices of the (basic) neighborhoods of $x$. Thus it is clear that $\varepsilon$ is one-to-one. To prove that it is continuous, we need only note:

$$\{x \mid n \in \varepsilon(x)\} = U_n,$$

which is always open. To show that $\varepsilon$ is an embedding, we must finally check that the *images* of the open sets $U_n$ are open in $\varepsilon(X)$. This comes down to showing:

$$\varepsilon(U_n) = \varepsilon(X) \cap \{z \mid n \in z\},$$

which is clear.

**For Section 2.** Equation (2.1) defines a continuous function because it is a special case of Theorem 1.5, where we have been able to simplify the definition into cases because $\omega$ is a very elementary subset of $\mathbf{P}\omega$. Equation (2.2) gives a continuous function since the definition makes $\hat{p}$ distributive, as remarked in the text for finite unions, but it is just as easy to show that $\hat{p}$ distributes over arbitrary unions. The difference between a continuous $f$ and a distributive $\hat{p}$ is this: to find $m \in f(x)$ we need a finite subset $e_n \subseteq x$ with $m \in f(e_n)$; however, to find $m \in \hat{p}(x)$ we need only *one* element $n \in x$ with $m \in \hat{p}(\{n\}) = \hat{p}(n) = p(n)$. Continuous functions are generalizations of distributive functions. The generality is necessary. For example, in (2.3) we see another function $x; y$ distributive in each of its variables; but take care: the function $x; x$ is not distributive in $x$—there is no closure under substitution. This is just one reason why continuous functions are better. Another good example comes from (2.4) if you compare the functions $x$, $x + x$, $x + x + x$, etc.

Equations (2.5)–(2.7) are very elementary. Note that $z \supset x, y$ is distributive in each of its variables. We could write: $z \supset x, y = \hat{p}(z)$, where $p(0) = x$ and $p(n + 1) = y$, to show that it is distributive in $z$.

*Proof of Theorem 2.1.* If we did not use the $\lambda$-notation, then all LAMBDA-definable functions would be obtained by substitution from the first five (cf. Table 2). Since they are all seen to be continuous, the result would then follow by the substitution theorem (Theorem 1.3). Bringing in $\lambda$-abstraction means that we have to combine Theorem 1.3 with this fact:

**LEMMA.** *If $f(x, y, z, \cdots)$ is a continuous function of all its variables, then $\lambda x.\, f(x, y, z, \cdots)$ is a continuous function of the remaining variables.*

*Proof.* It is enough to consider one extra variable. We compute from the definition of $\lambda$ in Table 2 as follows:

$$\lambda x.\, f(x, y) = \{(n, m) \mid m \in f(e_n, y)\}$$

$$= \{(n, m) \mid \exists e_k \subseteq y.\; m \in f(e_n, e_k)\}$$

$$= \bigcup \{\{(n, m) \mid m \in f(e_n, e_k)\} \mid e_k \subseteq y\}$$

$$= \bigcup \{\lambda x.\, f(x, e_k) \mid e_k \subseteq y\}.$$

Thus $\lambda x.\, f(x, y)$ is continuous in $y$.

*Proof of Theorem 2.2.* The reason behind this result is the restriction to continuous functions. Theorem 2.1 shows that we cannot violate the restriction by giving definitions in LAMBDA, and the graph theorem (Theorem 1.2) shows that continuous functions correspond perfectly with their graphs.

The verification of $(\alpha)$ of Table 1 is obvious as the '$x$' in '$\lambda x.\,\tau$' is a bound variable. (Care should be taken in making the proviso that '$y$' is not otherwise free in $\tau$.) The same would of course hold for any other pair of variables. We do not bother very much about alphabetic questions.

The verification of $(\beta)$ is just a restatement of Theorem 1.2(i). Let $\tau$ define a function $f$ (of $x$). Then by definition $f(x) = \tau$ and $\lambda x.\,\tau = \mathbf{graph}(f)$. Also $\mathbf{fun}(u)(x)$ in the notation of Theorem 1.2 is the same as the binary operation $u(x)$ in the notation of LAMBDA. Thus in Theorem 1.2(i) if we apply both sides to $y$ we get nothing else than $(\beta)$.

Half of property $(\xi)$ is already implied by $(\beta)$: the implication from left to right. (Just apply both sides to $x$.) In the other direction, $\forall x.\,\tau = \sigma$ means that $\tau$ and $\sigma$ define the *same* function of $x$; thus, the two graphs must be equal.

*Remarks on other laws.* The failure of $(\eta)$ simply means that not every set in $\mathbf{P}\omega$ is the graph of a function. Condition (iii) of Theorem 1.2 is equivalent to saying that $u = \lambda x.\, u(x)$, in other words, $u$ is the graph of some function if and only if it is the graph of the function determined by $u$.

Law $(\mu)$ is the monotone property of application (in both variables); therefore, $(\mu)$ and $(\xi)$ together imply $(\xi^*)$ from left to right. Suppose that $\forall x.\,\tau \subseteq \sigma$; then clearly:

$$\{(n, m) \mid m \in \tau[e_n / x]\} \subseteq \{(n, m) \mid m \in \sigma[e_n / x]\},$$

which gives $(\xi^*)$ from right to left.

There are, by the way, other laws valid in the model, as explained in the later results.

*Proof of Theorem 2.3.* This is a standard result in combinatory logic. We have only to put:

$$u = \lambda x_0 \lambda x_1 \cdots \lambda x_{n-1}.\, f(x_0, x_1, \cdots, x_{n-1}).$$

That is, we use the iteration of the process of forming the graph of a continuous function. As each step (from the inside out) keeps everything continuous, we are sure that the equation of Theorem 2.3 will hold for iterated application.

*Proof of Theorem 2.4.* This can be found in almost any reference on combinatory logic or $\lambda$-conversion. The main idea is to eliminate the $\lambda$ in favor of the combinators. The fact that we have a few other kinds of terms causes no problem if we introduce the corresponding combinators. The method of proof is to show, for any LAMBDA-term $\tau$ with free variables among $x_0, x_1, \ldots, x_{n-1}$, that there is a combination $\gamma$ of combinators such that:

$$\tau = \gamma(x_0)(x_1) \cdots (x_{k-1}).$$

This can be done by induction on the complexity of $\tau$.

*Proof of Theorem 2.5.* The well-known calculation shows that we have from (2.8):

$$\mathbf{Y}(u) = (\lambda x.\, u(x(x)))(\lambda x.\, u(x(x))) = u(\mathbf{Y}(u)).$$

Thus $\mathbf{Y}(u)$ is a fixed point of the function $u(x)$. What is needed is the proof to show that it is the least one.

Let $d = \lambda x.\, u(x(x))$ and let $a$ be any other fixed point of $u(x)$. To show, as we must, that $d(d) \subseteq a$, it is enough to show that $e_l \subseteq d$ always implies $e_l(e_l) \subseteq a$; because by continuity we have:

$$d(d) = \bigcup \{e_l(e_l) \mid e_l \subseteq d\}.$$

By way of induction, suppose that this implication holds for all $n < l$. Assume that $e_l \subseteq d$ and that $m \in e_l(e_l)$. We will want to use the induction hypothesis to show that $m \in a$. By the definition of application, there exists an integer $n$ such that $(n, m) \in e_l$ and $e_n \subseteq e_l$. But $n \le (n, m) < l$, and $e_n \subseteq d$. By the hypothesis, we have $e_n(e_n) \subseteq a$. Note that $(n, m) \in d$ also, and that $d$ is defined by $\lambda$-abstraction; thus, $m \in d(e_n)$ by definition. By monotonicity $u(e_n(e_n)) \subseteq u(a) = a$; therefore $m \in a$. This shows that $e_l(e_l) \subseteq a$, and the inductive proof is complete.

*Remark.* Note that we did not actually use the fixed-point theorem in the proof, but we did use rather special properties of the pairing $(n, m)$ and the finite sets $e_l$.

Equation (2.9) is proved easily from the definition of application; indeed $u(x)$ is distributive in $u$. Equation (2.10) is proved even more easily from the definition of $\lambda$-abstraction. For (2.11), we see that the inclusion from left to right would hold in general by monotonicity. In the other direction, suppose $m \in f(x) \cap g(x)$. Then for suitable $k$ and $l$ we have $(k, m) \in f$ and $e_k \subseteq x$, also $(l, m) \in g$ and $e_l \subseteq x$. Let $e_n = e_k \cup e_l \subseteq x$. Because $f$ and $g$ are graphs, we can say $(n, m) \in f \cap g$; and thus $m \in (f \cap g)(x)$. This is the only point where we require the assumption on graphs. Equation (2.12) follows directly from the definition of abstraction. For (2.13), which generalizes (2.9), we can also argue directly from the definition of application. In the case of intersection it is easy to find $u_n$ such that $0 \in u_n(\top)$ for all $n$, but $\bigcap \{u_n \mid n \in \omega\} = \bot$.

Equation (2.14) is obvious because the least fixed point of the identity function must be $\bot$. A less mysterious definition would be $\bot = 0 - 1$, but the chosen one is more “logical”.

For (2.15) we note that by definition:

$$\lambda z.\, 0 = \{(n, m) \mid m \in 0\} = \{(n, 0) \mid n \in \omega\}.$$

Because $0 = (0, 0)$ and $1 = (1, 0)$, we get the hint. Equation (2.16) makes use of $\cup$ for iteration. If $x = 0 \cup (x + 1)$, then $x$ must contain all integers; hence $x = \top$. The iteration for $\cap$ in (2.17) is more complex. The fundamental equation we need is:

$$x \cap y = x \supset (y \supset 0, \bot),\, ((x - 1) \cap (y - 1)) + 1.$$

This says to compute the intersection of two sets $x$ and $y$, we first test whether $0 \in x$. If so, then test whether $0 \in y$. If so, then we know $0 \in x \cap y$. In the meantime we begin testing $x$ for positive elements. If we could compute (by the same program) the intersection $(x - 1) \cap (y - 1)$, then we would get the positive elements of the intersection $x \cap y$ by adding one. This is a very slow program, but we can argue by induction that it gives us all the desired elements. Of course, $\cap$ is the least function satisfying this equation.

In the case of (2.18) it is clear that we have:

$$\lambda x.\, \bot = \{(n, m) \mid m \in \bot\} = \bot;$$

$$\lambda x.\, \top = \{(n, m) \mid m \in \top\} = \top;$$

because in the last every integer is a (number of a) pair. Suppose now that $a = \lambda x.\, a$ and $a \neq \top$. Let $k$ be the least integer where $k \notin a$. Now $k = (n, m)$ for some $n$ and $m$. If $m \in a$, then $(n, m) \in a = \lambda x.\, a$; hence $m \notin a$. But $m \leq k$ and $k$ is minimal; therefore, $m = k$. But this is only possible if $k = m = n = 0$. Suppose further $a \neq \bot$ and that $l$ is the least integer where $l \in a$. Now $l = (i, j)$ with $j \in a$ and $j \leq l$. So $j = l$ and $l = j = i = 0$. This contradiction proves that $a = \bot$ or $a = \top$.

Equations (2.19)–(2.22) are definitions, and (2.23) is proved easily by induction on $i$. Equation (2.24) is also a definition. To prove (2.25) we note that $\{ u_i \mid i \in x \}$ is continuous (even: distributive) in $u$ and $x$. Thus, there is a continuous function $\mathbf{seq}(u)(x)$ giving this value. What is required is to prove that it is LAMBDA-definable. We see:

$$\mathbf{seq}(u)(x) = \{n \in u_0 \mid 0 \in x\} \cup \{m \in \bigcup \{u_{i+1} \mid i+1 \in x\} \mid \exists k.\, k+1 \in x\}$$

$$= x \supset u_0,\, \mathbf{seq}(\lambda t.\, u_{t+1})(x - 1);$$

that is, $\mathbf{seq}$ satisfies the fixed-point equation for $\mathbf{\$}$. Thus $\mathbf{\$} \subseteq \mathbf{seq}$. To establish the other inclusion we argue by induction on $i$ for:

$$\forall x, u.\, [i \in x \Rightarrow u_i \subseteq \mathbf{\$}(u)(x)]$$

This is easy by cases using what we are given about $\mathbf{\$}$ in (2.24); it implies that $\mathbf{seq} \subseteq \mathbf{\$}$. Note that:

$$\lambda n \in \omega.\, \tau = \lambda n \in \omega.\, \sigma \quad \text{iff} \quad \forall n \in \omega.\, \tau = \sigma.$$

For primitive recursive functions, even of several variables, there is no trouble in transcribing into LAMBDA-notation any standard definition—especially as we can use the abstraction operator $\lambda n \in \omega$. If we recall that every r.e. set $a$ has the form:

$$a = \{m \mid \exists n.\, p(n) = m + 1\},$$

where $p$ is primitive recursive, we then see that $a = \hat{p}(\top) - 1$. This means that every r.e. set is LAMBDA-definable.

*Proof of Theorem 2.6.* In case of a function of several variables, we remark:

$$\lambda x_0 \lambda x_1 \cdots \lambda x_{k-1}.\, f(x_0)(x_1) \cdots (x_{k-1})$$

$$= \{(n_0, (n_1, (\cdots, (n_{k-1}, m) \cdots))) \mid m \in f(e_{n_0})(e_{n_1}) \cdots (e_{n_{k-1}})\}.$$

This makes the implication from (i) to (ii) obvious. Conversely, if a graph $u$ is r.e., then from the definition of application we have:

$$m \in u(e_{n_0})(e_{n_1}) \cdots (e_{n_{k-1}}) \quad \text{iff} \quad (n_0, (n_1, (\cdots, (n_{k-1}, m) \cdots))) \in u,$$

which is r.e. in $m, n_0, n_1, \dots, n_{k-1}$. Therefore (i) and (ii) are equivalent.

We have already proved that (ii) implies (iii). For the converse we have only to show that all LAMBDA-definable sets are r.e. For this argument we could take advantage of the combinator theorem, (Theorem 2.4). Each of the six combinators are r.e., and there is no problem of showing that if $u$ and $x$ are r.e., then so is $u(x)$; because it is defined in such an elementary way with existential and bounded universal number quantifiers and with membership in $u$ and in $x$ occurring positively. Explicitly we have:

$$m \in u(x) \quad \text{iff} \quad \exists e_n \subseteq x.\, (n, m) \in u$$

$$\quad \text{iff} \quad \exists n\, \forall m < n\, [[m \in e_n \text{ implies } m \in x] \text{ and } (n, m) \in u].$$

**For Section 3.** For the proof of (3.1) we distinguish cases. In case $x = y = \bot$, we note that $\mathbf{cond}(\bot)(\bot) = \bot$ and $\bot(\bot) = \bot$, so the equation checks in this case. Recall:

$$\mathbf{cond}(x)(y) = \lambda z.\, z \supset x, y = \{(n, m) \mid m \in (e_n \supset x, y)\}.$$

We can show $0 \notin \mathbf{cond}(x)(y)$. Note first $0 = (n, m)$ iff $n = 0 = m$; furthermore, $e_0 = \bot$ and $\bot \supset x, y = \bot$; but $0 \notin \bot$. Also we have:

$$\mathbf{cond}(x)(y)(0) = x \quad \text{and} \quad \mathbf{cond}(x)(y)(1) = y;$$

so if either $x \neq \bot$ or $y \neq \bot$, then $\mathbf{cond}(x)(y) \neq \bot$. In this case, $\mathbf{cond}(x)(y)$ must contain *positive* elements. The result now follows.

Theorem 3.1 is obvious from the construction of $\mathbf{G}$, because $\mathbf{G}(\mathbf{G}) = 0$ and $\mathbf{G}(0)(0) = \mathbf{suc}$, and so the $\mathbf{G}(0)(i)$ give us all the other combinators.

The primitive recursive functions needed for (3.4)–(3.6) are standard. Equation (3.7) is a definition—if we rewrote it using the $\mathbf{Y}$-operator—and the proof of Theorem 3.2 is easy by induction. There is also no difficulty with (3.8)–(3.12). The idea of the proof of Theorem 3.3 is contained in the statement of the theorem itself. The proof of Theorem 3.4 is already outlined in the text.

*Proof of Theorem 3.5.* The argument is essentially the original one of Myhill–Shepherdson. Suppose $p$ is computable, total and extensional. Define:

$$q = \{(j, m) \mid m \in \mathbf{val}(p(\mathbf{fin}(j)))\},$$

where $\mathbf{fin}$ is primitive recursive, and for all $j \in \omega$:

$$\mathbf{val}(\mathbf{fin}(j)) = e_j.$$

Certainly $q \in \mathbf{RE}$, and we will establish the theorem if we can prove “continuity”:

$$\mathbf{val}(p(n)) = \bigcup \{\mathbf{val}(p(\mathbf{fin}(j))) \mid e_j \subseteq \mathbf{val}(n)\}.$$

We proceed by contradiction. Suppose first we have a $k \in \mathbf{val}(p(n))$, where $k \notin \mathbf{val}(p(\mathbf{fin}(j)))$ whenever $e_j \subseteq \mathbf{val}(n)$. Pick $r$ to be a primitive recursive function whose range is *not* recursive. Define $s$, primitive recursive, so that for all $m \in \omega$:

$$\mathbf{val}(s(m)) = \{j \in \mathbf{val}(n) \mid m \notin \{r(i) \mid i \leq j\}\}.$$

The set $\mathbf{val}(n)$ must be infinite, because $p$ is extensional, and if $\mathbf{val}(n) = e_j = \mathbf{val}(\mathbf{fin}(j))$, then $k \notin \mathbf{val}(p(\mathbf{fin}(j))) = \mathbf{val}(p(n))$. Note that $\mathbf{val}(s(m))$, as a subset of the infinite set, is *finite* if $m$ is in the range of $r$; otherwise it is equal to $\mathbf{val}(n)$. Again by the extensionality of $p$ we see that $k \in \mathbf{val}(p(s(m)))$ if and only if $m$ is *not* in the range of $r$. But this puts an r.e. condition on $m$ equivalent to a non-r.e. condition, which shows there is no such $k$.

For the second case suppose we have a $k \notin \mathbf{val}(p(n))$, where for a suitable $e_j \subseteq \mathbf{val}(n)$ it is the case that $k \in \mathbf{val}(p(\mathbf{fin}(j)))$. Define:

$$t = \lambda m \in \omega.\, e_j \cup (\mathbf{val}(m) \supset \mathbf{val}(n), \mathbf{val}(n)).$$

We have:

$$t(m) = \begin{cases} e_j & \text{if } \mathbf{val}(m) = \bot; \\ \mathbf{val}(n) & \text{if not.} \end{cases}$$

We choose $u$ primitive recursive, where:

$$\mathbf{val}(u(m)) = t(m).$$

By the choice of $k$, and by the extensionality of $p$, and by the fact that $\mathbf{val}(n) \neq e_j$, we have:

$$k \in \mathbf{val}(p(u(m))) \quad \text{iff} \quad t(m) = e_j$$
$$\quad \text{iff} \quad \mathbf{val}(m) = \bot.$$

But this is impossible, since one side is r.e. in $m$ and the other is not by Theorem 3.4. As both cases lead to contradiction, continuity is established and the proof is complete.

*Proof of Theorem 3.6.* Consider a degree $\mathbf{Deg}(a)$. This set is closed under application, because:

$$u(a)(v(a)) = \mathbf{S}(u)(v)(a),$$

and $\mathbf{S}(u)(v)$ is r.e. if both $u$ and $v$ are. Note that it also contains the element $\mathbf{G}$; hence, as a subalgebra, it is generated by $a$ and $\mathbf{G}$.

Let $A$ be any finitely generated subalgebra with generators $a'_0, a'_1, \dots, a'_{n-1}$. Consider the element $a = \mathbf{cond}(\langle a'_0, a'_1, \dots, a'_{n-1} \rangle)(\mathbf{G})$. As in the proof of Theorem 3.1, $a$ generates $A$ under application. It is then easy to see why $\mathbf{A} = \mathbf{Deg}(a)$.

*Proof of Theorem 3.7.* We first establish (3.16) and (3.17):

$$\mathbf{L} \circ \bar{u} \circ \mathbf{R} = \lambda x.\, \mathbf{L}(\bar{u}(\langle 0, x \rangle))$$
$$= \lambda x.\, \mathbf{L}(\langle 1, u, x \rangle)$$
$$= \lambda x.\, u(x).$$

$$\bar{u} \circ \bar{v} \circ \mathbf{R} = \lambda x.\, \bar{u}(\bar{v}(\langle 0, x \rangle))$$
$$= \lambda x.\, \bar{u}(\langle 1, v, x \rangle)$$
$$= \lambda x.\, \overline{u(v)}(x)$$
$$= \overline{u(v)}.$$

Now starting with any $u \in \mathbf{RE}$, we write $u = \tau$, where $\tau$ is formed from $\mathbf{G}$ by application alone. By (3.17), we can write $\bar{u}$ in terms of $\bar{\mathbf{G}}$ and $\mathbf{R}$ using only $\circ$. That is, $\bar{u}$ belongs to a special subsemigroup. In view of (3.16), we find that $\lambda x.\, u(x)$ belongs to that generated by $\mathbf{R}$, $\mathbf{L}$ and $\bar{\mathbf{G}}$. But

$$\mathbf{RE} \cap \mathbf{FUN} = \{\lambda x.\, u(x) \mid u \in \mathbf{RE}\},$$

and so the theorem is proved.

**For Section 4.** The notion of a *continuous lattice* is due to Scott (1970/71) and we shall not review all the facts here. One special feature of these lattices is that the lattice operations of meet and join ($\sqcap$ and $\sqcup$) are continuous (that is, commute with directed sups). As topological spaces, they can be characterized as those $T_0$-spaces satisfying the extension theorem (which we proved for $\mathbf{P}\omega$ in Theorem 1.5).

*Proof of Theorem 4.1.* Consider a continuous function $a$, and let $A = \{x \mid x = a(x)\}$. By the fixed-point theorem (Theorem 1.4) we know that $A$ is nonempty and that it has a least element under $\subseteq$. Certainly $A$ is partially ordered by $\subseteq$; further, $A$ is closed under *directed* unions but not under arbitrary unions.
That is, $A$ is not a complete sublattice of $\mathbf{P}\omega$ with regard to the lattice operations of $\mathbf{P}\omega$, but it could be a complete lattice on its own—if we can show sups exist. Thus, let $S \subseteq A$ be an arbitrary subset of $A$. By the fixed-point theorem, find the least solution to the equation:

$$y = \bigcup \{x \mid x \in S\} \cup a(y).$$

Clearly $x \subseteq y$ for all $x \in S$; and so $x = a(x) \subseteq a(y)$, for all $x \in S$. This means that $y = a(y)$, and thus $y \in A$. By construction, then, $y$ is an upper bound to the elements of $S$. Suppose $z \in A$ is another upper bound for $S$. It will also satisfy the above equation; thus $y \subseteq z$, and so $y$ is the least upper bound. A partially ordered set with sups also has infs, as is well known, and is a complete lattice.

Suppose that $a$ is a retract. We can easily show that the fixed-point set $A$ (with the relative topology from $\mathbf{P}\omega$) satisfies the extension theorem. For assume $f : X \to A$ is continuous, and $X \subseteq Y$ as a subspace. Now we can also regard $f : X \to \mathbf{P}\omega$ as continuous because $A$ is a subspace of $\mathbf{P}\omega$. By Theorem 1.5 there is an extension to a continuous $\bar{f} : Y \to \mathbf{P}\omega$. But then $a \circ \bar{f} : Y \to A$ is the continuous function we want for $A$, and the proof is complete.

*The space of retracts.* Let us define:

$$\mathbf{RET} = \{a \mid a = a \circ a\},$$

the set of all retracts, which is a complete lattice in view of Theorem 4.1. It will be proved to be not a retract itself by showing it is not a continuous lattice; in fact, the meet operation on $\mathbf{RET}$ is not continuous on $\mathbf{RET}$.

The proof was kindly communicated by Y. L. Ershov and rests on distinguishing some extreme cases of retracts. Call a retract $a$ *nonextensive* if for all nonempty finite sets $x$ we have $x \not\subseteq a(x)$. Call a retract $b$ *finite* if all its values are finite (i.e., $b(\top)$ is finite). If $a$ is nonextensive and $b$ is finite, then Ershov notes that they are “orthogonal” in $\mathbf{RET}$ in the sense that $c = a \sqcap b = \bot$. The reason is that, since $c \subseteq b$, it is finite; but $c \subseteq a$, too, so $c(x) \subseteq a(x)$ for all $x$. Because $c$ is a retract, we have $c(x) = c(c(x)) \subseteq a(c(x))$. As $c(x)$ is finite and $a$ is nonextensive, it follows that $c(x) = \bot$ for all $x$.

This orthogonality is unfortunate, because consider the finite retracts $b_n = \lambda x.\, e_n$. We have here a directed set of retracts where $\bigcup \{b_n \mid n \in \omega\} = \lambda x.\, \top = \top$. If $\sqcap$ were continuous, it would follow that for nonextensive $a$:

$$a = a \sqcap \top = a \sqcap \bigcup \{b_n \mid n \in \omega\} = \bigcup \{a \sqcap b_n \mid n \in \omega\} = \bot,$$

showing that there are no nontrivial such $a$. But this is not so.

Let $\ll$ be a strict linear ordering of $\omega$ in the order type of the rational numbers. Define:

$$a(x) = \{m \mid \exists n \in x.\, m \ll n\}.$$

We see at once that $a$ is continuous; and, because $\ll$ is transitive and dense, $a$ is a retract. Since $\ll$ is irreflexive, it is the case for finite nonempty sets $x$ that $\max_\ll(x) \notin a(x)$; hence, $a$ is nonextensive. As $a(\top) = \top$, we find $a \neq \bot$. The proof is complete.

Note that there are many transitive, dense, irreflexive relations on $\omega$, so there are many nonextensive retracts. These retracts, like $a$ above, are *distributive*.

A nondistributive example is:

$$a' = \{m \mid \exists n, n' \in x.\, n \ll m \ll n'\}.$$

Many other examples are possible.

*Proof of Theorem 4.2.* The relation $\sqsubseteq$ is by the definition of retract reflexive on $\mathbf{RET}$; it is also obviously antisymmetric. To prove transitivity, suppose $a \sqsubseteq b \sqsubseteq c$, then

$$a = a \circ b = a \circ b \circ c = a \circ c.$$

Similarly, $a = c \circ a$. Note, by the way, that $a \sqsubseteq b$ implies that the range of $a$ is included in that of $b$; but that the relationship $a \subseteq b$ does not imply this fact. The relationship $a \sqsubseteq b$, however, is stronger than inclusion of ranges.

*Proofs of Theorems 4.3–4.5.* We will not give full details as all the parts of these theorems are direct calculations. Consider by way of example Theorem 4.3(i). We find:

$$(a \circ\to b) \circ (a \circ\to b) = \lambda u.\, b \circ (b \circ u \circ a) \circ a$$
$$= \lambda u.\, b \circ u \circ a$$
$$= a \circ\to b,$$

provided that $a$ and $b$ are retracts. A very similar computation would verify part (iv), if one writes out the composition:

$$(a \circ\to b') \circ (f \circ\to f') \circ (b \circ\to a')$$

and uses the equations:

$$f = b \circ f \circ a \quad \text{and} \quad f' = b' \circ f' \circ a'.$$

The main point of the proof of Theorem 4.6 has already been given in the text.

**For Sections 5–7.** Sufficient hints for proofs have been given in the text.
