# Function spaces

**3. FUNCTION SPACES.** We recall the standard definition and introduce our notation for function spaces.

**3.1 Definition.** For $T_0$-spaces $X$ and $Y$ we let $[X \to Y]$ be the *space of all continuous functions* $f : X \to Y$ endowed with the product topology, sometimes called the topology of pointwise convergence. This topology has as a subbase sets of the form:

$$ f : f(x) \in U $$

where $x \in X$ and $U \subseteq Y$ is open.

The pointwise aspect of the topology is immediately apparent in the partial ordering.

**3.2 Proposition.** *The induced partial ordering on $[X \to Y]$ is such that:*

$$f \sqsubseteq g \quad \text{iff} \quad f(x) \sqsubseteq g(x) \text{ for all } x \in X,$$

where $f, g \in [X \to Y]$. $\square$

where $f, g \in [X \to Y]$. $\square$

The first question, of course, is what kind of a partial ordering this is.

**3.3 Theorem.** If $D$ and $D'$ are continuous lattices, then so is $[D \to D']$ under the induced partial ordering with the lattice topology agreeing with the product topology.

**Proof:** The argument is "pointwise." Thus, the constant function with value $\bot \in D'$ is obviously continuous and is the $\bot$ of $[D \to D']$ by 3.2. Since by 2.7 the lattice operation $\sqcup$ on $D'$ is continuous, then if $f, g \in [D \to D']$ the composition $f \sqcup g$, defined by

$$(f \sqcup g)(x) = f(x) \sqcup g(x)$$

for all $x \in D$, is also continuous and represents the lub of $f, g$ in $[D \to D']$. (The same arguments apply to $\top$ and $\sqcap$, so $[D \to D']$ is at least a lattice.) To show that $[D \to D']$ is complete it is sufficient now to show that lubs of directed subsets exist. So let $\mathcal{F} \subseteq [D \to D']$ be directed. Define a function from $D$ into $D'$ by the equation:

$$(\bigsqcup \mathcal{F})(x) = \bigsqcup f(x) : f \in \mathcal{F},$$

for all $x \in D$. If we can show that $\bigsqcup \mathcal{F}$ is continuous, then being in $[D \to D']$ it has to be the lub. Consider $U \subseteq D'$, an open subset. Taking the inverse image and remembering that $\mathcal{F}$ is directed, we find:

$$x : (\bigsqcup \mathcal{F})(x) \in U = \bigcup x : f(x) \in U : f \in \mathcal{F}.$$

This is an open set, and so $\bigsqcup \mathcal{F}$ is indeed continuous. (Warning: the infinite $\sqcap \mathcal{F}$ are not in general computed pointwise; however, it is easy to extend the above argument to show that arbitrary $\bigsqcup \mathcal{F}$ are.)

To show that $[D \to D']$ is continuous, we establish first that for $f \in [D \to D']$

$$f = \bigsqcup \overrightarrow{e}[e, e'] : e' \ll f(e),$$

where $e$ ranges over $D$ and $e'$ over $D'$, and where the function $\overrightarrow{e}[e, e']$ is defined by:

$$\overrightarrow{e}[e, e'](x) = \begin{cases} e' & \text{if } e \ll x,  \bot & \text{if not,} \end{cases}$$

for all $x \in D$. Call the function on the right $f'$. Calculate:

$$
f'(x) = \bigsqcup \overrightarrow{e}[e, e'](x) : e' \ll f(e)
$$

$$
= \bigsqcup  e' : \exists e \ll x\ [e' \ll f(e)] 
$$

$$
= \bigsqcup  e' : e' \ll f(x)  = f(x).
$$

With the equation for $f$ proved, note next that for all $g \in [D \to D']$, $e' \ll g(e)$ implies $\overrightarrow{e}[e, e'] \sqsubseteq g$ by an easy pointwise argument. If we let $V =  g : e' \ll g(e) $, we see then that $V$ is open in the product topology and that $\overrightarrow{e}[e, e'] \sqsubseteq \sqcap V$. We may then conclude that $f = \bigsqcup  \sqcap V : f \in V $, which proves both that $[D \to D']$ is a continuous lattice and that the two topologies agree by the remark following 2.4. $\square$

The above theorem might possibly be generalized to $[X \to D]$ where $X$ is merely a $T_0$-space, but I was unable to see the argument. In any case we are mostly interested in the continuous lattices. Note as a consequence of our proof:

**3.4 Corollary.** For continuous lattices $D$ and $D'$, the evaluation map:

$$
\mathrm{eval} : [D \to D'] \times D \to D'
$$

is continuous.

**Proof:** Here $\mathrm{eval}(f, x) = f(x)$. With $f$ fixed, this is obviously continuous. With $x$ fixed, we proved the continuity above with our calculation of $\bigsqcup \mathcal{F}$ in view of 2.5. Hence applying 5.3 and 2.6, we conclude that $\mathrm{eval}$ is jointly continuous. $\square$

This result gives only one example of the masses of continuous functions that are available on continuous lattices. As another fundamental example we have:

**3.5 Proposition.** For continuous lattices $D$, $D'$, and $D''$, the map of functional abstraction:

$$
\mathrm{lambda} : [[D \times D'] \to D''] \to [D \to [D' \to D'']]
$$

is continuous.

**Proof:** Here lambda is defined by:

$$
\mathrm{lambda}(f)(x)(y) = f(x,y)
$$

where $f \in [[D \times D'] \to D'']$ and $x \in D$ and $y \in D'$. What is particularly interesting here is that by virtue of 3.3 we are making use of $[D \to [D' \to D'']]$ as a continuous lattice. The principle being stated here can be formulated more broadly in this way:

> If an expression $\mathcal{E}(x, y, z, \dots)$ is continuous in all its variables $x, y, z, \dots$ with values in $D'$ as $x$ ranges in $D$, then the expression
>
> $$\lambda x : D . \mathcal{E}(x, y, z, \dots)$$
>
> with values in $[D \to D']$ is continuous in the remaining variables $y, z, \dots$ .

The $\lambda$-notation is a notation for functions, where in the above the variable after the $\lambda$ is the *argument* and the expression after the $.$ is the *value* (as a function of the argument). Thus we could write:

$$
\mathrm{lambda} = \lambda f : [[D \times D'] \to D''] . \lambda x : D . \lambda y : D' . f(x,y),
$$

and, because $f(x,y)$ is continuous in $f$, $x$, and $y$, our conclusion follows. But often it is more readable not to write equations between functions but rather equations between values for definitional purposes.

The proof of the principle is easy. For let the variable $y$, say range over $D''$ and let $S \subseteq D''$ be a directed subset. Then

$$
\begin{aligned}
\lambda x : D . \mathcal{E}(x, \bigsqcup S, z, \dots) &= \lambda x : D . \bigsqcup  \mathcal{E}(x, y, z, \dots) : y \in S  
&= \bigsqcup  \lambda x : D . \mathcal{E}(x, y, z, \dots) : y \in S ,
\end{aligned}
$$

because the lubs of functions are computed pointwise. $\square$

We need not enumerate the many corollaries that follow easily now from this result. We mention, however, that composition $f \circ g$ of functions (on continuous lattices) is continuous in the two function variables, where we write

$$
(f \circ g)(x) = f(g(x)).
$$

What will be useful will be to return at this point to a discussion of the injective properties of continuous lattices. If one continuous lattice is a subspace of another it is of course a retract. This relationship between spaces can be given by a pair of continuous maps

$$i : D \to D' \quad \text{and} \quad j : D' \to D,$$

where

$$j \circ i = \text{id}_D = \lambda x : D . x.$$

The composition $i \circ j : D' \to i(D)$ is the retraction onto the subspace corresponding to $D$ under $i$. Now if we have a diagram:

$$
\begin{gathered}
D \xrightarrow[\ j\ ]{i} D' 
f \searrow \qquad \swarrow \tilde{f} = f \circ j 
D''
\end{gathered}
$$

the given continuous $f$ is at once extendable from $D$ to $D'$ by the obvious definition of $\tilde{f}$. This $\tilde{f}$ is not the $\bar{f}$ used in the proof of 2.11, and it will be well to sort out the connections. On one side note that if $f'$ is any function which extends $f$, then we have $f = f' \circ i$. But this implies

$$\tilde{f} = f \circ j = f' \circ i \circ j,$$

which shows that $\tilde{f}$ is a "degraded" version of $f'$. There is one situation where this type of degrading is especially nice.

**3.6 Definition.** A continuous lattice $D$ is said to be a *projection* of a continuous lattice $D'$ iff there are a pair of continuous maps

$$i : D \to D' \quad \text{and} \quad j : D' \to D$$

such that not only

$$j \circ i = \text{id}_D,$$

but also

$$i \circ j \sqsubseteq \text{id}_{D'}.$$

Thus, in case our retraction is a projection, we have $\tilde{f} \sqsubseteq f'$, which means that $\tilde{f}$ is the *minimal* extension of $f \in [D \to D'']$ to a function in $[D' \to D'']$. We will discuss the nature of $\tilde{f}$ in a moment. But before we do we pause to remark that the correspondence $f \rightsquigarrow \tilde{f}$ is *continuous*, and this fact is easily extended.

**3.7 Proposition.** Suppose the two pairs of maps

$$i_n : D_n \to D'_n \quad \text{and} \quad j_n : D'_n \to D_n$$

for $n = 0,1$ make $D_n$ a retraction (projection) of $D'_n$. Then $[D_0 \rightarrow D_1]$ is also a retraction (projection) of $[D'_0 \rightarrow D'_1]$ by means of the pair of maps:

$$\vec{i}(f) = i_1 \circ f \circ j_0 \text{ , and}$$

$$\vec{j}(f') = j_1 \circ f' \circ i_0 \text{ ,}$$

where $f \in [D_0 \rightarrow D_1]$ and $f' \in [D'_0 \rightarrow D'_1]$. $\square$

Returning now to $\bar{f}$ we can prove:

**3.8 Proposition.** If $D$ is a continuous lattice and $e : X \rightarrow Y$ a subspace embedding, then for each $f : X \rightarrow D$, the function $\bar{f} : Y \rightarrow D$ given by the formula

$$\bar{f}(y) = \bigsqcup  \sqcap  f(x) : e(x) \in U  : y \in U ,$$

where $U$ ranges over open subsets of $Y$ and $x$ over $X$, is the maximal extension of $f$ to a function in the partially ordered set $[Y \rightarrow D]$.

**Proof:** We are saying that $\bar{f}$ is the maximal solution to the equation

$$f = \bar{f} \circ e.$$

We already know it is a solution, so let $f'$ be any other. We have

$$
\begin{aligned}
f'(y) &= \bigsqcup  \sqcap  f'(z) : z \in U  : y \in U  
&\sqsubseteq \bigsqcup  \sqcap  f'(z) : z \in e(X) \cap U  : y \in U  
&= \bigsqcup  \sqcap  f'(e(x)) : e(x) \in U  : y \in U  
&= \bigsqcup  \sqcap  f(x) : e(x) \in U  : y \in U  
&= \bar{f}(y),
\end{aligned}
$$

which establishes that $f' \sqsubseteq \bar{f}$. $\square$

By the same argument we could show that $\bar{f}$ is the maximal solution of $\bar{f} \circ e \sqsubseteq f$. An interesting question is whether the correspondence $f \rightsquigarrow \bar{f}$ is continuous. I very much doubt it, but at this moment a counterexample escapes me. It is clear that the correspondence is monotonic, for if $f \sqsubseteq g$, then the formula of 3.8 shows that $\bar{f} \sqsubseteq \bar{g}$. This gives us a neat argument for the previous remark: if $g \circ e \sqsubseteq f$, then

$$\overline{g \circ e} \sqsubseteq \bar{f}.$$

But $g \circ e = \overline{g \circ e} \circ e$, so by 3.8, $g \sqsubseteq \overline{g \circ e}$, and $\bar{f}$ is thus maximal.

In the case that the range spaces are being extended, the following lemma relating the extensions will be very useful when we consider inverse limits.

**3.9 Lemma.** Consider the diagram:

$$
\begin{gathered}
X \xrightarrow{\quad e\quad} Y 
f \Big\downarrow \qquad\qquad g \searrow \qquad \bar{f} \swarrow \qquad \downarrow \bar{g} 
D \xrightarrow[\ j\ ]{\quad i\quad} D'
\end{gathered}
$$

where the upper row is a subspace embedding and the lower is a projection. If the given functions $f$ and $g$ are extended to $\bar{f}$ and $\bar{g}$ as in 3.8, and if $f = j \circ g$, then $\bar{f} = j \circ \bar{g}$ also.

*Proof:* $\bar{f}$ and $\bar{g}$ are maximal solutions of $f = \bar{f} \circ e$ and $g = \bar{g} \circ e$. Therefore since

$$
f = j \circ g = j \circ \bar{g} \circ e,
$$

we see that

$$
j \circ \bar{g} \sqsubseteq \bar{f}.
$$

Note also that

$$
i \circ \bar{f} \circ e = i \circ f = i \circ j \circ g \sqsubseteq g,
$$

and so by the remark following 3.8, we have

$$
i \circ \bar{f} \sqsubseteq \bar{g}.
$$

Therefore

$$
\bar{f} = j \circ i \circ \bar{f} \sqsubseteq j \circ \bar{g},
$$

which proves the equality. $\square$

Whether this lemma is true for retractions in any form, I do not know. My proof seems to require the stronger projection relationship. I suspect there may be difficulties. In general projections are better behaved than retractions. By the way the word projection seems to be properly used in 3.6, for the projection $j : D \times D' \to D$ of the Cartesian product of two continuous lattices onto the first factor *is* a projection with partial inverse $i : D \to D \times D'$ defined by

$$
i(x) = (x, \bot)
$$

for $x \in D$.

**3.10 Proposition.** If the continuous lattice $D$ is a projection of the continuous lattice $D'$ via the pair of maps $i, j$; then for all $S \subseteq D$ and all $x, y \in D$ we have:

(i) $i(\bigsqcup S) = \bigsqcup i(x) : x \in S$,

(ii) $i(x) = i(y)$ implies $x = y$,

(iii) $x \ll y$ implies $i(x) \ll i(y)$.

Conversely, if a map $i : D \to D'$ satisfies (i)–(iii), then there exists a continuous $j : D' \to D$ making $D$ a projection of $D'$, and in fact $j$ is uniquely determined by:

(iv) $j(x') = \bigsqcup x \in D : i(x) \sqsubseteq x'$

for all $x' \in D'$.

**Proof:** Equation (i) holds for directed $S \subseteq D$ because $i$ is continuous. To have it hold for arbitrary $S$ it is only necessary to check it for finite sets, because every lub is the directed lub of finite sublubs. (The last word of that sentence is an unfortunate accident.) Further, to check the equation for finite sets it is enough to check it for the empty set and for two element sets. Thus, $i(\bot) = \bot$, because $j(i(\bot)) = \bot$ and since $\bot \sqsubseteq i(\bot)$,

$$
j(\bot) \sqsubseteq j(i(\bot)) = \bot,
$$

so $j(\bot) = \bot$. Whence $i(\bot) = i(j(\bot)) \sqsubseteq \bot$. Next $i(x \sqcup y) = i(x) \sqcup i(y)$, because first

$$
i(x) \sqcup i(y) \sqsubseteq i(x \sqcup y)
$$

by monotonicity. Then note that

$$
i(x) \sqsubseteq i(x) \sqcup i(y)
$$

and so

$$
x = j(i(x)) \sqsubseteq j(i(x) \sqcup i(y)).
$$

Similarly

$$
y \sqsubseteq j(i(x) \sqcup i(y)),
$$

whence

$$
x \sqcup y \sqsubseteq j(i(x) \sqcup i(y)).
$$

But then

$$
i(x \sqcup y) \sqsubseteq i(j(i(x) \sqcup i(y))) \sqsubseteq i(x) \sqcup i(y),
$$

which completes the argument for equation (i).

Condition (ii) is obvious. For (iii) we argue as follows. Assume $x \ll y$. Since $D'$ is continuous we can write:

$$i(y) = \bigsqcup  z' \in D' : z' \ll i(y) ,$$

and conclude by the continuity of $j$ that:

$$y = j(i(y)) = \bigsqcup  j(z') : z' \ll i(y) .$$

But $x \ll y$, so $x \ll j(z')$ for some $z' \ll i(y)$. Now $x \sqsubseteq j(z')$ follows; therefore $i(x) \sqsubseteq i(j(z')) \sqsubseteq z'$. Thus $i(x) \ll i(y)$.

Turning now to the converse, assume of the map $i$ that it satisfies (i)–(iii). Compute:

$$i(j(x')) = \bigsqcup  i(x) : i(x) \sqsubseteq x'  \sqsubseteq x'.$$

This is correct because $i$ is continuous and the set $ x : i(x) \sqsubseteq x' $ is directed in view of condition (i). Thus $i \circ j \sqsubseteq \mathrm{id}_{D'}$. Note that by virtue of (i) and (ii) it is the case that

$$i(x) \sqsubseteq i(y) \text{ implies } x \sqsubseteq y.$$

(The reason is that $x \sqsubseteq y$ is equivalent to $x \sqcup y = y$.) This remark allows us to compute:

$$j(i(y)) = \bigsqcup  x : i(x) \sqsubseteq i(y) $$
$$= \bigsqcup  x : x \sqsubseteq y  = y.$$

Hence, $j \circ i = \mathrm{id}_D$. It remains to show that $j$ is continuous. Suppose $S' \subseteq D'$ is directed. Since $j$ is by definition monotonic, it is sufficient to prove that

$$j(\bigsqcup S') \sqsubseteq \bigsqcup  j(x') : x' \in S' .$$

Now

$$j(\bigsqcup S') = \bigsqcup  x : i(x) \sqsubseteq \bigsqcup S' ,$$

so suppose $i(x) \sqsubseteq \bigsqcup S'$. Let $z \ll x$; whence $i(z) \ll i(x)$. Thus $i(z) \ll x'$ for some $x' \in S'$, and therefore $i(z) \sqsubseteq x'$. We obtain then $z \sqsubseteq j(x')$, which means that

$$z \sqsubseteq \bigsqcup  j(x') : x' \in S' $$

holds for all $z \ll x$. By the continuity of $D$ we conclude

$$x \sqsubseteq \bigsqcup  j(x') : x' \in S' $$

holds for all $x$ with $i(x) \sqsubseteq \bigsqcup S'$. The desired result follows. $\square$

As a corollary of 3.10 we can easily see which *subspaces* of a continuous lattice $D'$ are projections of it. Such a subspace $D \subseteq D'$ must first be closed under $\bigsqcup$. That is, if $S \subseteq D$, then $\bigsqcup S \in D$ for

all $S$, where the lub is taken in the sense of $D'$. The identity map on $D$ will then satisfy (i) and (ii). But this is not enough, since we would not know that $D$ is a continuous lattice, nor whether (iii) holds. The following additional condition would be sufficient, if assumed for all $y \in D$:

$$y = \bigsqcup x \in D : x \ll y,$$

where $\ll$ is taken in the sense of $D'$. This implies that

$$y = \bigsqcup \sqcap (D \cap U) : y \in U$$

where $U$ ranges over the open subsets of $D'$ and where the $\sqcap$ is taken in the sense of $D$. This condition makes the subspace topology the same as the lattice topology on $D$ and besides makes $D$ continuous, which is just what we need. (Another way to put it is that whenever $z \ll y$, where $y \in D$ but $z \in D'$, then $z \sqsubseteq x \ll y$, for some $x \in D$.)

It seems a bit troublesome to characterize in a simple way just which maps $j : D' \to D$ are projections. (Other than saying outright that the map $i : D \to D'$ such that for all $x \in D$:

$$i(x) = \sqcap x' \in D' : x \sqsubseteq j(x')$$

is the continuous partial inverse to $j$.) But we can say very easily which continuous maps $j : D' \to D'$ are projections onto *subspaces*; namely, we must have

$$j = j \circ j \sqsubseteq \mathrm{id}.$$

The subspace in question then is:

$$D = x \in D' : j(x) = x.$$

This non-empty subspace is the exact range of $j$ and is closed under $\bigsqcup$. Let $y \in D$. Then if $x' \ll y$ in $D'$, we find $j(x') \sqsubseteq x' \ll y$. Thus since

$$y = \bigsqcup x' \in D' : x' \ll y,$$

we see that

$$y = j(y) = \bigsqcup j(x') : x' \ll y.$$

But each $j(x') \in D$, so $y = \bigsqcup x \in D : x \ll y$, as desired.

The foregoing discussion suggests looking more closely at the space of all projections of a continuous lattice since they are so easily characterized.

**3.11 Definition.** Given a continuous lattice $D$, we let the space of projections be denoted by:

$$J_D = j \in [D \to D] : j = j \circ j \sqsubseteq \mathrm{id}.$$

**3.12 Proposition.** For a continuous lattice $D$ the space $J_D$ of projections forms a complete lattice as a $\bigsqcup$-closed subspace of $[D \to D]$.

**Proof:** The constant function $\bot \in J_D$ obviously, so $J_D$ contains $\bigsqcup \emptyset$. Suppose $j, k \in J_D$. We wish to show that $j \sqcup k \in J_D$. Compute:

$$(j \sqcup k)((j \sqcup k)(x)) = j(j(x) \sqcup k(x)) \sqcup k(j(x) \sqcup k(x)).$$

But note:

$$j(x) \sqsubseteq j(j(x)) \sqsubseteq j(j(x) \sqcup k(x)) \sqsubseteq j(x),$$

because $j(x) \sqcup k(x) \sqsubseteq x$. Similarly for $k(x)$. Therefore, we find that $(j \sqcup k) \circ (j \sqcup k) = j \sqcup k \sqsubseteq \mathrm{id}$.

Suppose finally that $S \subseteq J_D$ is directed. We wish to show that $\bigsqcup S \in J_D$. Clearly $\bigsqcup S \sqsubseteq \mathrm{id}$, so compute by continuity of $\circ$:

$$\bigsqcup S \circ \bigsqcup S = \bigsqcup j \circ j : j \in S = \bigsqcup j : j \in S = \bigsqcup S.$$

It follows that $J_D$ is $\bigsqcup$-closed and hence is a complete lattice. $\square$

The significance of the above result becomes clearer if we consider the connection between projections and subspaces. Let us write:

$$D(j) = x \in D : j(x) = x.$$

For $j \in J_D$, each $D(j)$ is a projection of $D$ onto a subspace. We show first that

$$j \sqsubseteq k \quad \text{iff} \quad D(j) \subseteq D(k).$$

Because if $j \sqsubseteq k$, then $j \sqsubseteq j \circ j \sqsubseteq k \circ j \sqsubseteq \mathrm{id} \circ j = j$. Therefore if $j(x) = x$, then $k(x) = k(j(x)) = j(x) = x$, which means that $D(j) \subseteq D(k)$. On the other hand, if $D(j) \subseteq D(k)$, then since $j(D) \subseteq D(j)$, we see that $k \circ j = j$, and so $j \sqsubseteq k \circ \mathrm{id} = k$. Hence $J_D$ is isomorphic to the partially ordered set of subspaces of $D$ that are projections. We thus conclude that these subspaces form a lattice. In fact, it is easy to show that

$$D(j \sqcup k) = x \sqcup y : x \in D(j), y \in D(k).$$

Similarly, if $S$ is a directed set of $J_D$, then $D(\bigsqcup S)$ is the $\bigsqcup$-closure in $D$ of the subset:

$$\bigcup D(j) : j \in S.$$

These are not very deep facts, but their proofs were very much facilitated by the introduction of $J_D$ and the utilization of the lattice structure of $[D \to D]$. Along the same line we can define for $j, k \in J_D$ a function $(j \to k) \in [D \to D] \to [D \to D]$ by the equation

$$(j \to k)(f) = k \circ f \circ j.$$

It is very easy to show that $(j \to k) \in J_{[D \to D]}$, that $(j \to k)$ is continuous in $j$ and $k$, and that $[D \to D](j \to k)$ is isomorphic to $[D(j) \to D(k)]$. There are many other interesting operations on projections corresponding to other constructs besides these. And, just as with $(j \to k)$, the operations are continuous. This makes it possible to prove existence theorems about subspaces by using results like the fixed-point theorem for continuous functions. It would be even nicer if $J_D$ turns out to be a continuous lattice itself, but as far as I can tell this is not likely to be the case.

Before we turn to the iterated function-space construction by inverse limits, there are a couple of other connections between spaces and function spaces that are useful to know.

**3.13 Proposition.** Every continuous lattice $D$ is a projection of its function space $[D \to D]$.

**Proof:** Consider the following pair of mappings $\mathrm{con} : D \to [D \to D]$ and $\mathrm{min} : [D \to D] \to D$ where

$$\mathrm{con}(x)(y) = x$$

and

$$\mathrm{min}(f) = f(\bot)$$

for all $x, y \in D$ and $f \in [D \to D]$. They are obviously continuous. The map $\mathrm{con}$ matches every element of $D$ with the corresponding *constant* function in $[D \to D]$. The map $\mathrm{min}$ associates to every function in $[D \to D]$ its *minimum* value in the partial ordering. The proof that this pair forms a projection is trivial. $\square$

The pair $\mathrm{con}$, $\mathrm{min}$ are not the only pair for making $D$ a projection of $[D \to D]$. The following pair of maps were suggested by David Park:

$$\lambda x.\vec{e}[t,x] \quad \text{and} \quad \lambda f. f(t),$$

where $x$ ranges over $D$, and $f$ over $[D \to D]$, and where $t$ is a fixed *isolated* element of $D$ (that is, $t \ll t$ holds). The pair $\mathrm{con}$ and $\mathrm{min}$ will result if we set $t = \bot$. (Note that the expression $\vec{e}[t,x]$, though continuous in $x$, is not continuous—or even monotonic—in the variable $t$.) A lattice may very well possess a large number of isolated

elements, whence a large number of projections. And furthermore this is the only way the function $j = \lambda f. f(t)$ can be a projection. For assume the existence of an inverse $i : D \to [D \to D]$ satisfying the proper conditions. Then it would be the case that

$$i(x)(t) = x$$

and

$$i(f(t))(y) \sqsubseteq f(y)$$

for all $x, y \in D$ and all $f \in [D \to D]$. We can prove for all $u \in D$, if $t \not\sqsubseteq u$, then

$$i(x)(u) = \bot$$

by substituting $\vec{e}[v,x]$ for $f$ in the second equation above, where $v$ is chosen so that $v \ll t$ but not $v \ll u$. But then note that

$$i(x)(t) = \bigsqcup i(x)(u) : u \ll t.$$

If not $t \ll t$, then $u \ll t$ implies $t \not\sqsubseteq u$, which leads to absurdity. Hence $t$ must be isolated, and, as we noted earlier, the function $i$ is uniquely determined as being the one we already knew. Aside from these pairs of projections one could obtain others by combinations with automorphisms. I was unable to determine whether there are further pairs of an essentially different nature.

The topic of projections in these spaces is rather interesting since one has in a way more freedom in $T_0$-spaces (particularly in injective spaces) than in ordinary spaces for defining functions. As another example, consider the Cartesian square $D \times D$. Aside from the two obvious projections onto $D$, there is also the “diagonal” system given by the pair:

$$\lambda x.(x,x) \qquad \text{and} \qquad \lambda (x,y). x \sqcap y$$

We shall note in the next section how the choice of an initial projection effects the construction of an inverse limit.

The projections are not the only useful functions in $[D \to D] \to D$. As a final example of what can be done in function spaces we mention the fixed-point operator.

**3.14 Proposition.** *For a continuous lattice $D$ there is a uniquely determined continuous mapping*

$$\mathrm{fix} : [D \to D] \to D$$

*where for all $f \in [D \to D]$ and $x \in D$*

$$f(\mathrm{fix}(f)) = \mathrm{fix}(f)$$

and whenever $f(x) \sqsubseteq x$, then $\mathrm{fix}(f) \sqsubseteq x$.

and whenever $f(x) \sqsubseteq x$, then

$$\mathrm{fix}(f) \sqsubseteq x.$$

**Proof:** The proof of the existence of minimal fixed points in complete lattices is well known, as was mentioned in the proof of 2.10.

To establish the continuity, it is sufficient to remark that since all functions $f \in [D \to D]$ are continuous, we have

$$\mathrm{fix}(f) = \bigsqcup_{n=0}^{\infty} f^n(\bot),$$

where $f^n(x) = f(f(\ldots f(x) \ldots))$ ($n$ times). Thus $\mathrm{fix}$ is the point-wise lub of continuous functions on $[D \to D]$ and is thus itself continuous. $\square$

**Lean 4**

- [ContinuousLattice/FunctionSpaces.lean](DomainTheory/ContinuousLattice/FunctionSpaces.lean)
- [ContinuousLattice/FunctionSpaces/Basic.lean](DomainTheory/ContinuousLattice/FunctionSpaces/Basic.lean)
- [ContinuousLattice/FunctionSpaces/Basic/isLUB_sSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/Basic/isLUB_sSup.lean)
- [ContinuousLattice/FunctionSpaces/BasicInst28.lean](DomainTheory/ContinuousLattice/FunctionSpaces/BasicInst28.lean)
- [ContinuousLattice/FunctionSpaces/BasicInst30.lean](DomainTheory/ContinuousLattice/FunctionSpaces/BasicInst30.lean)
- [ContinuousLattice/FunctionSpaces/BasicInst33.lean](DomainTheory/ContinuousLattice/FunctionSpaces/BasicInst33.lean)
- [ContinuousLattice/FunctionSpaces/IsContinuousLatticeProjection.lean](DomainTheory/ContinuousLattice/FunctionSpaces/IsContinuousLatticeProjection.lean)
- [ContinuousLattice/FunctionSpaces/IsContinuousLatticeRetraction.lean](DomainTheory/ContinuousLattice/FunctionSpaces/IsContinuousLatticeRetraction.lean)
- [ContinuousLattice/FunctionSpaces/IsProjection.lean](DomainTheory/ContinuousLattice/FunctionSpaces/IsProjection.lean)
- [ContinuousLattice/FunctionSpaces/Projections.lean](DomainTheory/ContinuousLattice/FunctionSpaces/Projections.lean)
- [ContinuousLattice/FunctionSpaces/ScottMap.lean](DomainTheory/ContinuousLattice/FunctionSpaces/ScottMap.lean)
- [ContinuousLattice/FunctionSpaces/ScottMapProjection.lean](DomainTheory/ContinuousLattice/FunctionSpaces/ScottMapProjection.lean)
- [ContinuousLattice/FunctionSpaces/ScottMapRetraction.lean](DomainTheory/ContinuousLattice/FunctionSpaces/ScottMapRetraction.lean)
- [ContinuousLattice/FunctionSpaces/ambientSSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/ambientSSup.lean)
- [ContinuousLattice/FunctionSpaces/bot.lean](DomainTheory/ContinuousLattice/FunctionSpaces/bot.lean)
- [ContinuousLattice/FunctionSpaces/bot_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/bot_apply.lean)
- [ContinuousLattice/FunctionSpaces/comp.lean](DomainTheory/ContinuousLattice/FunctionSpaces/comp.lean)
- [ContinuousLattice/FunctionSpaces/comp_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/comp_apply.lean)
- [ContinuousLattice/FunctionSpaces/con_.lean](DomainTheory/ContinuousLattice/FunctionSpaces/con_.lean)
- [ContinuousLattice/FunctionSpaces/con_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/con_apply.lean)
- [ContinuousLattice/FunctionSpaces/const.lean](DomainTheory/ContinuousLattice/FunctionSpaces/const.lean)
- [ContinuousLattice/FunctionSpaces/const_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/const_apply.lean)
- [ContinuousLattice/FunctionSpaces/continuousMapInducedPiTopology.lean](DomainTheory/ContinuousLattice/FunctionSpaces/continuousMapInducedPiTopology.lean)
- [ContinuousLattice/FunctionSpaces/converseProjection.lean](DomainTheory/ContinuousLattice/FunctionSpaces/converseProjection.lean)
- [ContinuousLattice/FunctionSpaces/converseRetr.lean](DomainTheory/ContinuousLattice/FunctionSpaces/converseRetr.lean)
- [ContinuousLattice/FunctionSpaces/converseRetr_incl.lean](DomainTheory/ContinuousLattice/FunctionSpaces/converseRetr_incl.lean)
- [ContinuousLattice/FunctionSpaces/converseRetr_mono.lean](DomainTheory/ContinuousLattice/FunctionSpaces/converseRetr_mono.lean)
- [ContinuousLattice/FunctionSpaces/converseRetr_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/converseRetr_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4.lean](DomainTheory/ContinuousLattice/FunctionSpaces/corollary_3_4.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4_eval_on_C.lean](DomainTheory/ContinuousLattice/FunctionSpaces/corollary_3_4_eval_on_C.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4_jointly_continuous.lean](DomainTheory/ContinuousLattice/FunctionSpaces/corollary_3_4_jointly_continuous.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/corollary_3_4_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/curry_left_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/curry_left_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/curry_right_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/curry_right_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/directedOn_finsetSupOf.lean](DomainTheory/ContinuousLattice/FunctionSpaces/directedOn_finsetSupOf.lean)
- [ContinuousLattice/FunctionSpaces/finsetSupOf.lean](DomainTheory/ContinuousLattice/FunctionSpaces/finsetSupOf.lean)
- [ContinuousLattice/FunctionSpaces/fix.lean](DomainTheory/ContinuousLattice/FunctionSpaces/fix.lean)
- [ContinuousLattice/FunctionSpaces/fixMap.lean](DomainTheory/ContinuousLattice/FunctionSpaces/fixMap.lean)
- [ContinuousLattice/FunctionSpaces/fix_eq.lean](DomainTheory/ContinuousLattice/FunctionSpaces/fix_eq.lean)
- [ContinuousLattice/FunctionSpaces/fix_le.lean](DomainTheory/ContinuousLattice/FunctionSpaces/fix_le.lean)
- [ContinuousLattice/FunctionSpaces/fix_mono.lean](DomainTheory/ContinuousLattice/FunctionSpaces/fix_mono.lean)
- [ContinuousLattice/FunctionSpaces/fix_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/fix_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/fix_unique.lean](DomainTheory/ContinuousLattice/FunctionSpaces/fix_unique.lean)
- [ContinuousLattice/FunctionSpaces/idMap.lean](DomainTheory/ContinuousLattice/FunctionSpaces/idMap.lean)
- [ContinuousLattice/FunctionSpaces/idMap_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/idMap_apply.lean)
- [ContinuousLattice/FunctionSpaces/image_retr_wayBelow_directed.lean](DomainTheory/ContinuousLattice/FunctionSpaces/image_retr_wayBelow_directed.lean)
- [ContinuousLattice/FunctionSpaces/image_retr_wayBelow_nonempty.lean](DomainTheory/ContinuousLattice/FunctionSpaces/image_retr_wayBelow_nonempty.lean)
- [ContinuousLattice/FunctionSpaces/incl_bot.lean](DomainTheory/ContinuousLattice/FunctionSpaces/incl_bot.lean)
- [ContinuousLattice/FunctionSpaces/incl_converseRetr_le.lean](DomainTheory/ContinuousLattice/FunctionSpaces/incl_converseRetr_le.lean)
- [ContinuousLattice/FunctionSpaces/incl_finset_sup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/incl_finset_sup.lean)
- [ContinuousLattice/FunctionSpaces/incl_injective.lean](DomainTheory/ContinuousLattice/FunctionSpaces/incl_injective.lean)
- [ContinuousLattice/FunctionSpaces/incl_mono_of_preservesSSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/incl_mono_of_preservesSSup.lean)
- [ContinuousLattice/FunctionSpaces/incl_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/incl_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/incl_sSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/incl_sSup.lean)
- [ContinuousLattice/FunctionSpaces/incl_sup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/incl_sup.lean)
- [ContinuousLattice/FunctionSpaces/incl_sup_of_preservesSSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/incl_sup_of_preservesSSup.lean)
- [ContinuousLattice/FunctionSpaces/incl_wayBelow.lean](DomainTheory/ContinuousLattice/FunctionSpaces/incl_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/instCompleteLattice.lean](DomainTheory/ContinuousLattice/FunctionSpaces/instCompleteLattice.lean)
- [ContinuousLattice/FunctionSpaces/instSupSet.lean](DomainTheory/ContinuousLattice/FunctionSpaces/instSupSet.lean)
- [ContinuousLattice/FunctionSpaces/isLUB_sSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/isLUB_sSup.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_bot.lean](DomainTheory/ContinuousLattice/FunctionSpaces/isProjection_bot.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_directedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/isProjection_directedSup.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_finsetSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/isProjection_finsetSup.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_iff.lean](DomainTheory/ContinuousLattice/FunctionSpaces/isProjection_iff.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_sSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/isProjection_sSup.lean)
- [ContinuousLattice/FunctionSpaces/isProjection_sup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/isProjection_sup.lean)
- [ContinuousLattice/FunctionSpaces/lambda_outer_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/lambda_outer_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/le.lean](DomainTheory/ContinuousLattice/FunctionSpaces/le.lean)
- [ContinuousLattice/FunctionSpaces/le_antisymm'.lean](DomainTheory/ContinuousLattice/FunctionSpaces/le_antisymm'.lean)
- [ContinuousLattice/FunctionSpaces/le_def.lean](DomainTheory/ContinuousLattice/FunctionSpaces/le_def.lean)
- [ContinuousLattice/FunctionSpaces/le_of_incl_le.lean](DomainTheory/ContinuousLattice/FunctionSpaces/le_of_incl_le.lean)
- [ContinuousLattice/FunctionSpaces/le_refl'.lean](DomainTheory/ContinuousLattice/FunctionSpaces/le_refl'.lean)
- [ContinuousLattice/FunctionSpaces/le_sSup_finsetSupOf.lean](DomainTheory/ContinuousLattice/FunctionSpaces/le_sSup_finsetSupOf.lean)
- [ContinuousLattice/FunctionSpaces/le_trans'.lean](DomainTheory/ContinuousLattice/FunctionSpaces/le_trans'.lean)
- [ContinuousLattice/FunctionSpaces/lemma_3_9_incl_inf.lean](DomainTheory/ContinuousLattice/FunctionSpaces/lemma_3_9_incl_inf.lean)
- [ContinuousLattice/FunctionSpaces/lemma_3_9_retr_inf.lean](DomainTheory/ContinuousLattice/FunctionSpaces/lemma_3_9_retr_inf.lean)
- [ContinuousLattice/FunctionSpaces/lt.lean](DomainTheory/ContinuousLattice/FunctionSpaces/lt.lean)
- [ContinuousLattice/FunctionSpaces/lt_iff_le_not_ge'.lean](DomainTheory/ContinuousLattice/FunctionSpaces/lt_iff_le_not_ge'.lean)
- [ContinuousLattice/FunctionSpaces/mem_finsetSupOf_of_mem.lean](DomainTheory/ContinuousLattice/FunctionSpaces/mem_finsetSupOf_of_mem.lean)
- [ContinuousLattice/FunctionSpaces/min.lean](DomainTheory/ContinuousLattice/FunctionSpaces/min.lean)
- [ContinuousLattice/FunctionSpaces/min_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/min_apply.lean)
- [ContinuousLattice/FunctionSpaces/monotone.lean](DomainTheory/ContinuousLattice/FunctionSpaces/monotone.lean)
- [ContinuousLattice/FunctionSpaces/pointwiseSubbasic_isOpen.lean](DomainTheory/ContinuousLattice/FunctionSpaces/pointwiseSubbasic_isOpen.lean)
- [ContinuousLattice/FunctionSpaces/pointwiseSubbasic_scottOpen.lean](DomainTheory/ContinuousLattice/FunctionSpaces/pointwiseSubbasic_scottOpen.lean)
- [ContinuousLattice/FunctionSpaces/pointwise_sSup_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/pointwise_sSup_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/pointwise_sup_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/pointwise_sup_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/preservesDirectedSup_coe.lean](DomainTheory/ContinuousLattice/FunctionSpaces/preservesDirectedSup_coe.lean)
- [ContinuousLattice/FunctionSpaces/projection.lean](DomainTheory/ContinuousLattice/FunctionSpaces/projection.lean)
- [ContinuousLattice/FunctionSpaces/proposition_2_10.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_2_10.lean)
- [ContinuousLattice/FunctionSpaces/proposition_2_10_a.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_2_10_a.lean)
- [ContinuousLattice/FunctionSpaces/proposition_2_10_b.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_2_10_b.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_10_converse.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_10_converse.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_10_forward.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_10_forward.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_12.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_12.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_13.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_13.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_14.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_14.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_2.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_2.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_5.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_5.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_5_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_5_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_7_projection.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_7_projection.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_7_retraction.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_7_retraction.lean)
- [ContinuousLattice/FunctionSpaces/retr_ambientSSup_eq_sSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/retr_ambientSSup_eq_sSup.lean)
- [ContinuousLattice/FunctionSpaces/retr_bot.lean](DomainTheory/ContinuousLattice/FunctionSpaces/retr_bot.lean)
- [ContinuousLattice/FunctionSpaces/retr_eq_sSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/retr_eq_sSup.lean)
- [ContinuousLattice/FunctionSpaces/retr_wayBelow_of_wayBelow_incl.lean](DomainTheory/ContinuousLattice/FunctionSpaces/retr_wayBelow_of_wayBelow_incl.lean)
- [ContinuousLattice/FunctionSpaces/sInf_image_le_sInf_image_of_subset.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sInf_image_le_sInf_image_of_subset.lean)
- [ContinuousLattice/FunctionSpaces/sSupMaps.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sSupMaps.lean)
- [ContinuousLattice/FunctionSpaces/sSupMaps_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sSupMaps_apply.lean)
- [ContinuousLattice/FunctionSpaces/sSupMaps_continuous.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sSupMaps_continuous.lean)
- [ContinuousLattice/FunctionSpaces/sSup_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sSup_apply.lean)
- [ContinuousLattice/FunctionSpaces/sSup_finsetSupOf.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sSup_finsetSupOf.lean)
- [ContinuousLattice/FunctionSpaces/sSup_image_prod_mk_left.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sSup_image_prod_mk_left.lean)
- [ContinuousLattice/FunctionSpaces/sSup_image_prod_mk_right.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sSup_image_prod_mk_right.lean)
- [ContinuousLattice/FunctionSpaces/sSup_image_retr_wayBelow.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sSup_image_retr_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/sSup_le_finsetSupOf.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sSup_le_finsetSupOf.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionEvalSubbasis.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottFunctionEvalSubbasis.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionSpecializationLe.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottFunctionSpecializationLe.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionSubbasis_isOpen.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottFunctionSubbasis_isOpen.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionSubbasis_isOpen_scott.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottFunctionSubbasis_isOpen_scott.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionTopology.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottFunctionTopology.lean)
- [ContinuousLattice/FunctionSpaces/scottFunctionTopology_eq_induced_pi.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottFunctionTopology_eq_induced_pi.lean)
- [ContinuousLattice/FunctionSpaces/scottLambda.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottLambda.lean)
- [ContinuousLattice/FunctionSpaces/scottLambdaAt.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottLambdaAt.lean)
- [ContinuousLattice/FunctionSpaces/scottLambda_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottLambda_apply.lean)
- [ContinuousLattice/FunctionSpaces/scottMapInducedPiTopology.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottMapInducedPiTopology.lean)
- [ContinuousLattice/FunctionSpaces/scottMapPointwiseSubbasis.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottMapPointwiseSubbasis.lean)
- [ContinuousLattice/FunctionSpaces/scottMapPointwiseTopology.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottMapPointwiseTopology.lean)
- [ContinuousLattice/FunctionSpaces/scottMapPointwiseTopology_eq_induced_pi.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottMapPointwiseTopology_eq_induced_pi.lean)
- [ContinuousLattice/FunctionSpaces/scottMap_eq_sSup_openInfs.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottMap_eq_sSup_openInfs.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtend.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtend.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_eq_of_comp.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_eq_of_comp.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_eq_of_ext.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_eq_of_ext.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_le_of_mem.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_le_of_mem.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono_incl.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono_incl.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono_incl_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono_incl_apply.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono_retr.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtendInf_mono_retr.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtend_eq_of_ext.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtend_eq_of_ext.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtend_maximal.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtend_maximal.lean)
- [ContinuousLattice/FunctionSpaces/scottSubspaceExtend_mono.lean](DomainTheory/ContinuousLattice/FunctionSpaces/scottSubspaceExtend_mono.lean)
- [ContinuousLattice/FunctionSpaces/specializationLe_generateOpen.lean](DomainTheory/ContinuousLattice/FunctionSpaces/specializationLe_generateOpen.lean)
- [ContinuousLattice/FunctionSpaces/stepFun.lean](DomainTheory/ContinuousLattice/FunctionSpaces/stepFun.lean)
- [ContinuousLattice/FunctionSpaces/stepFun_of_not_wayBelow.lean](DomainTheory/ContinuousLattice/FunctionSpaces/stepFun_of_not_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/stepFun_of_wayBelow.lean](DomainTheory/ContinuousLattice/FunctionSpaces/stepFun_of_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/stepFun_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/stepFun_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaces/stepMap.lean](DomainTheory/ContinuousLattice/FunctionSpaces/stepMap.lean)
- [ContinuousLattice/FunctionSpaces/stepMap_apply_of_wayBelow.lean](DomainTheory/ContinuousLattice/FunctionSpaces/stepMap_apply_of_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/stepMap_le_of_wayBelow.lean](DomainTheory/ContinuousLattice/FunctionSpaces/stepMap_le_of_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/stepMap_pointwise_sSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/stepMap_pointwise_sSup.lean)
- [ContinuousLattice/FunctionSpaces/stepMap_wayBelow.lean](DomainTheory/ContinuousLattice/FunctionSpaces/stepMap_wayBelow.lean)
- [ContinuousLattice/FunctionSpaces/sup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sup.lean)
- [ContinuousLattice/FunctionSpaces/sup_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaces/sup_apply.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3.lean](DomainTheory/ContinuousLattice/FunctionSpaces/theorem_3_3.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3_isContinuousLattice.lean](DomainTheory/ContinuousLattice/FunctionSpaces/theorem_3_3_isContinuousLattice.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3_sSup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/theorem_3_3_sSup.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3_sup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/theorem_3_3_sup.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3_topology.lean](DomainTheory/ContinuousLattice/FunctionSpaces/theorem_3_3_topology.lean)
- [ContinuousLattice/FunctionSpaces/theorem_3_3_topology_induced_pi.lean](DomainTheory/ContinuousLattice/FunctionSpaces/theorem_3_3_topology_induced_pi.lean)
- [ContinuousLattice/FunctionSpaces/toOrderHom.lean](DomainTheory/ContinuousLattice/FunctionSpaces/toOrderHom.lean)
- [ContinuousLattice/FunctionSpaces/wayBelow_finset_sup.lean](DomainTheory/ContinuousLattice/FunctionSpaces/wayBelow_finset_sup.lean)
- [ContinuousLattice/FunctionSpaces/wayBelow_le_finset_sup_step.lean](DomainTheory/ContinuousLattice/FunctionSpaces/wayBelow_le_finset_sup_step.lean)
- [ContinuousLattice/Theorem212/lemma_3_9.lean](DomainTheory/ContinuousLattice/Theorem212/lemma_3_9.lean)
