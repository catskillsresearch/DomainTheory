# Proposition 3.14

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

- [ContinuousLattice/FunctionSpaces/proposition_3_14.lean](proposition_3_14.lean)
