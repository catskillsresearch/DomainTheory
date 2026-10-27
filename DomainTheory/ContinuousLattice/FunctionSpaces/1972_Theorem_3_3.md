# Theorem 3.3

The first question, of course, is what kind of a partial ordering this is.

**3.3 Theorem.** If $D$ and $D'$ are continuous lattices, then so is $[D \to D']$ under the induced partial ordering with the lattice topology agreeing with the product topology.

**Proof:** The argument is "pointwise." Thus, the constant function with value $\bot \in D'$ is obviously continuous and is the $\bot$ of $[D \to D']$ by 3.2. Since by 2.7 the lattice operation $\sqcup$ on $D'$ is continuous, then if $f, g \in [D \to D']$ the composition $f \sqcup g$, defined by

$$(f \sqcup g)(x) = f(x) \sqcup g(x)$$

for all $x \in D$, is also continuous and represents the lub of $f, g$ in $[D \to D']$. (The same arguments apply to $\top$ and $\sqcap$, so $[D \to D']$ is at least a lattice.) To show that $[D \to D']$ is complete it is sufficient now to show that lubs of directed subsets exist. So let $\mathcal{F} \subseteq [D \to D']$ be directed. Define a function from $D$ into $D'$ by the equation:

$$(\bigsqcup \mathcal{F})(x) = \bigsqcup f(x) : f \in \mathcal{F},$$

for all $x \in D$. If we can show that $\bigsqcup \mathcal{F}$ is continuous, then being in $[D \to D']$ it has to be the lub. Consider $U \subseteq D'$, an open subset. Taking the inverse image and remembering that $\mathcal{F}$ is directed, we find:

$$\{ x : (\bigsqcup \mathcal{F})(x) \in U \} = \bigcup \{ \{ x : f(x) \in U \} : f \in \mathcal{F} \}.$$

This is an open set, and so $\bigsqcup \mathcal{F}$ is indeed continuous. (Warning: the infinite $\sqcap \mathcal{F}$ are not in general computed pointwise; however, it is easy to extend the above argument to show that arbitrary $\bigsqcup \mathcal{F}$ are.)

To show that $[D \to D']$ is continuous, we establish first that for $f \in [D \to D']$

$$f = \bigsqcup \overrightarrow{e}[e, e'] : e' \ll f(e),$$

where $e$ ranges over $D$ and $e'$ over $D'$, and where the function $\overrightarrow{e}[e, e']$ is defined by:

$$\overrightarrow{e}[e, e'](x) = \begin{cases} e' & \text{if } e \ll x,  \bot & \text{if not,} \end{cases}$$

for all $x \in D$. Call the function on the right $f'$. Calculate:

$$
f'(x) = \bigsqcup \{ \overrightarrow{e}[e, e'](x) : e' \ll f(e) \}
$$

$$
= \bigsqcup \{ e' : \exists e \ll x,\; e' \ll f(e) \}
$$

$$
= \bigsqcup \{ e' : e' \ll f(x) \} = f(x).
$$

With the equation for $f$ proved, note next that for all $g \in [D \to D']$, $e' \ll g(e)$ implies $\overrightarrow{e}[e, e'] \sqsubseteq g$ by an easy pointwise argument. If we let $V = \{ g : e' \ll g(e) \}$, we see then that $V$ is open in the product topology and that $\overrightarrow{e}[e, e'] \sqsubseteq \sqcap V$. We may then conclude that $f = \bigsqcup \{ \sqcap V : f \in V \}$, which proves both that $[D \to D']$ is a continuous lattice and that the two topologies agree by the remark following 2.4. $\square$
