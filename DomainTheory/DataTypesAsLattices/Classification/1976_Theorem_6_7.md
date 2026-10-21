# Theorem 6.7

**THEOREM 6.7 (The $\mathfrak{B}_\delta$ theorem).** *The sets that are countable intersections of Boolean combinations of open sets are exactly the sets of the form:*

$$\{x \mid f(x) = g(x)\},$$

*where $f, g : \mathbf{P}\omega \to \mathbf{P}\omega$ are continuous.*

This is clearly the most interesting of these characterization theorems, because equations like $f(x) = g(x)$ turn up all the time and the collection is a very rich totality of subsets of $\mathbf{P}\omega$. It includes all the retracts, since they are of the form $\{x \mid x = a(x)\}$. And much more. That every such set in Theorem 6.7 is $\mathfrak{B}_\delta$ follows from these logical transformations:

$$\{x \mid f(x) = g(x)\} = \{x \mid \forall n \in \omega [n \in f(x) \leftrightarrow n \in g(x)]\}$$

$$= \bigcap_{n=0}^{\infty} (\{x \mid n \in f(x), n \in g(x)\} \cup \{x \mid n \notin f(x), n \notin g(x)\})$$

That puts the set in the class $(\mathfrak{F} \cup \mathfrak{G})_\delta = \mathfrak{B}_\delta$.

On the other hand, we can see that $(\mathfrak{F} \cup \mathfrak{G})_\sigma$ is exactly $\mathfrak{B}_\delta$. Because, in view of Theorem 6.6, $\mathfrak{B}_\sigma$, the class of *countable* unions of $\mathfrak{B}$-sets, is exactly $(\mathfrak{F} \dot{\cap} \mathfrak{G})_\sigma$. The remark we want to make then follows by taking complements.

Now let $S$ be an arbitrary $\mathfrak{B}_\delta$-set. We can write:

$$S = \bigcap_{n=0}^{\infty} (\{x \mid f_n(x) = 0\} \cup \{x \mid g_n(x) = 0\}),$$

where $f_n, g_n : \mathbf{P}\omega \to \{\bot, 0, \top\}$ are continuous. Now let $u, v$ be continuous functions which on $\{\bot, 0, \top\}$ realize these two tables:

| $u$ | $\bot$ | $0$ | $\top$ |
| :---: | :---: | :---: | :---: |
| $\bot$ | $\bot$ | $0$ | $0$ |
| $0$ | $0$ | $0$ | $0'$ |
| $\top$ | $0$ | $0'$ | $0'$ |

| $v$ | $\bot$ | $0$ | $\top$ |
| :---: | :---: | :---: | :---: |
| $\bot$ | $0$ | $0$ | $0'$ |
| $0$ | $0$ | $0$ | $0'$ |
| $\top$ | $0'$ | $0'$ | $\top$ |

where $0' = 0 \cup \bot$. This is an exercise in many-valued logic, and we find for $x, y \in \{\bot, 0, \top\}$:

$$u(x)(y) = v(x)(y) \quad \text{iff} \quad x = 0 \text{ or } y = 0.$$

Thus define continuous functions $f'$ and $g'$ such

$$f' = \lambda x \lambda n \in \omega . u(f_n(x))(g_n(x)),$$
$$g' = \lambda x \lambda n \in \omega . v(f_n(x))(g_n(x)),$$

and we find:

$$S = \{x \mid f'(x) = g'(x)\}$$

as desired.

This is as far as we can go with *equations*. More complicated sets can be defined using *quantifiers*, for example the $\Sigma_1^1$ or *analytic* sets can be put in the form:

$$\{x \mid \exists y . f(x)(y) = g(x)(y)\},$$

and their complements, the $\Pi_1^1$ sets, in the form

$$\{x \mid \forall y \exists z . h(x)(y)(z) = 0\},$$

with continuous $f, g, h$. For the three classes we then have as “typical” sets those shown in Table 3.

It should be remarked that $\mathfrak{B}_\delta$ contains all the closed sets in the *Cantor space* topology on $\mathbf{P}\omega$ (that is, the topology obtained when it is regarded as the infinite product of *discrete* two-point spaces). Therefore the $\Sigma_1^1$ sets for the two topologies on $\mathbf{P}\omega$ are the *same*. Hence, since we know for Cantor space that $\Delta_1^1 = \Sigma_1^1 \cap \Pi_1^1$ is the class of *Borel sets*, we can conclude that the two topologies on $\mathbf{P}\omega$ have the *same* Borel sets. (That is, in both cases $\Delta_1^1$ is the Boolean $\sigma$-algebra generated from the open sets.)

**TABLE 3** *Classes and typical sets*

| Classes | Typical sets |
| :--- | :--- |
| $\mathfrak{G}$ | $\{x \mid 0 \in x\}$ |
| $\mathfrak{F}$ | $\{\bot\}$ |
| $\mathfrak{G}_\delta$ | $\{\top\}$ |
| $\mathfrak{F} \dot{\cap} \mathfrak{G}$ | $\{0\}$ |
| $\mathfrak{F} \dot{\cap} \mathfrak{G}_\delta$ | $\{\top + 1\}$ |
| $\mathfrak{B}_\delta$ | $\{u \mid u_0 = u_1\}$ |
| $\Sigma_1^1$ | $\{u \mid \exists y.\, u_0(y) = u_1(y)\}$ |
| $\Pi_1^1$ | $\{u \mid \forall y \exists z.\, u(y)(z) = 0\}$ |

Returning now to the example involving trees mentioned at the beginning of this section, we see that the set of perfect (finite) trees can be written in the form:

$$\{x \mid x = \mathbf{tree}(x),\, \mathbf{perf}(x) = 0\} = \{x \mid \langle x,\, \mathbf{perf}(x) \rangle = \langle \mathbf{tree}(x),\, 0 \rangle\};$$

thus it is a $\mathfrak{B}_\delta$-set. (Note that $\mathfrak{B}_\delta$ are obviously closed under finite intersection by the ordered pair method just illustrated; that they are closed under finite union is a little messier to make explicit, but the essential idea is contained in the proof of Theorem 6.7.)

As another example, we might wish to allow infinite trees but not the strange tree $\top$. Consider the following function:

$$(6.4) \quad \mathbf{top} = \lambda u : \mathbf{tree}.\, \mathbf{which}(u) \sqsubseteq \bot,\, \mathbf{top}(\mathbf{fst}(\mathbf{out}(u))) \cup \mathbf{top}(\mathbf{snd}(\mathbf{out}(u))).$$

We can show that $\mathbf{top} : \mathbf{P}\omega \to \{\bot, \top\}$. For a tree $u$ the equation $\mathbf{top}(u) = \bot$ means that it *does not* contain $\top$, or as we might say: it is *topless*. The topless trees form a closed subset of the subspace of trees. (An interesting retract is the function $\lambda u.\, \mathbf{tree}(u) \cup \mathbf{top}(u)$ whose range consists exactly of the topless trees plus *one* exceptional tree $\top$.) Such a closed subset of (the range of) a retract is a kind of *semilattice*. (We shall not introduce a precise definition here.) Every directed subset has a limit (least upper bound) and every pair with an upper bound has a least upper bound. But generally least upper bounds do not have to exist within the semilattice. The type of domains that interest us *become* continuous lattices with the *addition* of a top element $\top$ larger than all the other elements. The elimination of $\top$ is done with a function like $\mathbf{top}$ of our example. This is convincing evidence to the author that an independent theory of semilattices is quite unnecessary: they can all be *derived* from lattices. The problem is simply to define the top-cutting operation, then restriction to the “topless” elements is indicated by an equation (like $\mathbf{top}(u) = \bot$). In this way all the constructions are kept within the control of a smooth-running theory based on **LAMBDA**. This point seems to be important if one wants to keep track of which functions are computable.

An aspect of the problem of classification treated in this section which has not been given close enough attention is the explicitly constructive way of verifying the closure properties of the classes. Consider the class $\mathfrak{B}_\delta$, for example. Let $B$ be the typical set as shown in Table 3. Then whatever $f \in \mathbf{P}\omega$ we choose, the set

$$\{x \mid f(x) \in B\}$$
is a $\mathfrak{B}_\delta$-set and every such set has this form. Thus the $f$'s *index* the elements of the class. Suppose $f, g \in \mathbf{P}\omega$. What we should look for are two LAMBDA-definable combinators such that $\mathbf{union}(f)(g)$ and $\mathbf{inter}(f)(g)$ give the functions that index the union and intersection of the sets determined by $f$ and $g$. That is, we want:

$$\{x \mid \mathbf{union}(f)(g)(x) \in B\} = \{x \mid f(x) \in B\} \cup \{x \mid g(x) \in B\}.$$

It should be possible to extract the precise definition from the outline of the proofs given above, but in general this matter needs more investigation. There may very well be certain classes where such operations are not constructive, even though the classes are simply defined.
