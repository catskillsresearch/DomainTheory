# Theorem 2.5

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

**Lean 4**

- [DataTypesAsLattices/Lambda/theorem_2_5.lean](theorem_2_5.lean)
- [DataTypesAsLattices/Lambda/dollarC_combinatory.lean](dollarC_combinatory.lean)
- [DataTypesAsLattices/Lambda/eq_2_24_Ycomb.lean](eq_2_24_Ycomb.lean)
- [DataTypesAsLattices/Lambda.lean](../Lambda.lean)
- [DataTypesAsLattices/Computability/Basic.lean](../Computability/Basic.lean)
