# Inverse limits

**4. INVERSE LIMITS.** By an *inverse system of spaces* we understand as usual a sequence

$$\langle X_n, j_n \rangle_{n=0}^{\infty}$$

of $T_0$-spaces and continuous maps $j_n : X_{n+1} \to X_n$. The space $X_{\infty}$, called the *inverse limit* of the sequence, is constructed in the familiar way as that subspace of the product space consisting of exactly those infinite sequences

$$x = \langle x_n \rangle_{n=0}^{\infty},$$

where for each $n$ we have $x_n \in X_n$, and

$$j_n(x_{n+1}) = x_n.$$

The space $X_{\infty}$ is given the product topology, and the maps $j_{\infty n} : X_{\infty} \to X_n$ such that

$$j_{\infty n}(x) = x_n$$

are of course continous and satisfy the recursion equation:

$$j_{\infty n} = j_n \circ j_{\infty(n+1)}.$$

Besides this we have the expected extension property for any system of continuous maps

$$f_n : Y \to X_n$$

where for each $n$

$$f_n = j_n \circ f_{n+1}.$$

Because, we can define

$$f_{\infty} : Y \to X_{\infty}$$

by the equation

$$f_{\infty}(y) = \langle f_n(y) \rangle_{n=0}^{\infty}$$

for all $y \in Y$; whence

$$f_n = j_{\infty n} \circ f_{\infty}$$

holds. So much for a review of inverse limits. In this paper our interest will center on rather special inverse systems and their limits.

**4.1 Proposition.** Let $\langle D_n, j_n \rangle_{n=0}^{\infty}$ be an inverse system of continuous lattices where each $j_n : D_{n+1} \to D_n$ is a projection. Then the inverse limit space $D_{\infty}$ is also a continuous lattice.

**Proof:** We need only show that $D_{\infty}$ as a $T_0$-space is injective. So suppose $f_{\infty} : X \to D_{\infty}$ is given and $X \subseteq Y$. Define $f_n : X \to D_n$ by $f_n = j_{\infty n} \circ f_{\infty}$. Let $\bar{f}*n : Y \to D_n$ be the maximal extension of $f_n$ according to 3.8. Now we can see the point of Lemma 3.9: by this construction we guarantee that $\bar{f}n = j_n \circ \bar{f}{n+1}$. Hence the required $\bar{f}*{\infty} : Y \to D_{\infty}$ exists. $\square$

I do not know at the time of writing whether this theorem on inverse limits of continuous lattices extends to sequences where, say, the $j_n$ are only retractions. Fortunately, sufficiently many projections exist to make this construction useful. Note that by reference to the product space construction of $D_{\infty}$, its lattice ordering is given simply by the relation:

$$x \sqsubseteq y \quad \text{iff} \quad x_n \sqsubseteq y_n \text{ for all } n.$$

**4.2 Proposition.** Let $\langle D_n, j_n \rangle_{n=0}^{\infty}$ and $D_{\infty}$ be as in 4.1. Then the maps $j_{\infty n} : D_{\infty} \to D_n$ are projections.

**Proof:** The projections $j_n : D_{n+1} \to D_n$, as we know, have their uniquely determined inverses $i_n : D_n \to D_{n+1}$. We can define $i_{n\infty} : D_n \to D_{\infty}$ by the equation:

$$i_{n\infty}(x) = \langle y_m \rangle_{m=0}^{\infty}$$

where

$$
y_m = \begin{cases}
j_m(y_{m+1}) & \text{if } m < n, 
x & \text{if } m = n, 
i_m(y_{m-1}) & \text{if } m > n.
\end{cases}
$$

The proof that $i_{n\infty}$ and $j_{\infty n}$ form a projection is now an easy computation. $\square$

One should note also the recursion equation:

$$
i_{n\infty} = i_{(n+1)\infty} \circ i_n.
$$

These maps also make it possible to state this useful equation:

$$
x = \bigsqcup_{n=0}^{\infty} i_{n\infty}(x_n),
$$

where $x \in D_\infty$. It is easy to check that this is a monotone lub, and so we can say each $x \in D_\infty$ is the limit of its projections $x_n$. In fact, from what we know about projections, $x_n$ is the best possible approximation to $x$ in the space $D_n$.

**4.3 Corollary.** Let the spaces be as in 4.1 and 4.2. Let $D'$ be any complete lattice and suppose continuous functions $f_n : D_n \to D'$ are given so that $f_n = f_{n+1} \circ i_n$. Then we can define $f_\infty : D_\infty \to D'$ by the equation:

$$
f_\infty(x) = \bigsqcup_{n=0}^{\infty} f_n(x_n)
$$

for $x \in D_\infty$, and we have $f_n = f_\infty \circ i_{n\infty}$. $\square$

The import of this last result is that within the category of complete lattices, the space $D_\infty$ is not only the inverse limit of the $D_n$, but it is also the *direct* limit. (One system of spaces here uses the $j_n$ as connecting maps, the other the $i_n$.) This is the algebraic result that lies at the heart of our main result about inverse limits of function spaces.

Turning to function spaces, let $D = D_0$ be a given continuous lattice. As we have seen in 3.13, there are many ways of making $D_0$ a projection of $D_1 = [D_0 \to D_0]$. Choose one such given by a pair $i_0, j_0$. Define recursively:

$$
D_{n+1} = [D_n \to D_n]
$$

and introduce the pairs $i_{n+1}, j_{n+1}$ making $D_{n+1}$ a projection of $D_{n+2}$ by the method of 3.7. Specifically we shall have for $x \in D_{n+1}$ and $x' \in D_{n+2}$:

$$
i_{n+1}(x) = i_n \circ x \circ j_n,
$$

$$
j_{n+1}(x') = j_n \circ x' \circ i_n.
$$

Since these spaces are more than continuous lattices being function spaces, it is interesting to note that the maps $i_n$ preserve function value as an algebraic operation as follows:

$$
i_n(f(x)) = i_{n+1}(f)(i_n(x)),
$$

where $x \in D_n$ and $f \in D_{n+1}$. Thus in passing to the limit space $D_\infty$ something of functional application must also be preserved. The precise result shows that indeed $D_\infty$ becomes its own function space.

**4.4 Theorem.** *The inverse limit $D_\infty$ of the recursively defined sequence $\langle D_n, j_n \rangle_{n=0}^{\infty}$ of function spaces is not only a continuous lattice, but it is also homeomorphic to its own function space $[D_\infty \to D_\infty]$.*

**Proof:** We can write down directly the pair of maps $i_\infty, j_\infty$ that provide the homeomorphism:

$$
i_\infty(x) = \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ x_{n+1} \circ j_{\infty n}),
$$

$$
j_\infty(f) = \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(j_{\infty n} \circ f \circ i_{n\infty}).
$$

Note that these formulae are simply generalizations at the limit for the formulae we used to define $i_n, j_n$ in the first place. Thus it is not surprising that they would provide a projection of $[D_\infty \to D_\infty]$ upon $D_\infty$. Indeed we can compute out $j_\infty(i_\infty(x))$, noting that all the lubs are monotone and that a double monotone limit can always be replaced by a single one in view of the continuity of the operations involved, obtaining

$$
\begin{aligned}
j_\infty(i_\infty(x)) &= \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(j_{\infty n} \circ i_{n\infty} \circ x_{n+1} \circ j_{\infty n} \circ i_{n\infty}) 
&= \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(x_{n+1}) 
&= x.
\end{aligned}
$$

In the converse order the calculation is only a bit more complicated. The idea is that since all the functions $f$ are continuous and since the elements $x$ are the limits of their approximations, then each $f$ is actually completely determined by its

In the converse order the calculation is only a bit more complicated. The idea is that since all the functions $f$ are continuous and since the elements $x$ are the limits of their approximations, then each $f$ is actually completely determined by its sequence of restrictions $j_{\infty n} \circ f \circ i_{n\infty} \in D_{n+1}$. This simple idea can be made more precise with the aid of a lemma about $D_\infty$, which allows us in certain cases to recognize projections from limits.

**4.5 Lemma.** Suppose for each $n$ we have $u_{(n+1)} \in D_{n+1}$ and we let:

$$u = \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(u_{(n+1)}).$$

Then if

$$j_{n+1}(u_{(n+2)}) = u_{(n+1)}$$

for each $n$, we can conclude that:

$$j_{\infty(n+1)}(u) = u_{(n+1)}.$$

**Proof:** If the sequence $u_{(n+1)}$ satisfies the recursion, then the limit defining $u$ is monotonic. Therefore by continuity of projection it suffices to prove that

$$j_{\infty(n+1)}(i_{(m+1)\infty}(u_{(m+1)})) = u_{(n+1)}$$

for all $m \geqslant n$. This is obvious for $m = n$, and it can be readily proved by induction for larger $m$ using the various recursion equations. (Properly speaking the induction is done on the quantity $(m - n)$ using both $n$ and $m$ as variables.) $\square$

**Proof of 4.4 concluded:** The lemma applies at once to our calculation, for we find:

$$
\begin{aligned}
i_\infty(j_\infty(f)) &= \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n} \circ f \circ i_{n\infty} \circ j_{\infty n}) 
&= \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n}) \circ f \circ \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n}).
\end{aligned}
$$

Here we have just applied the continuity of $f$ to be able to confine the lub on the right. But now by the remark following 4.2, we note the functional equation:

$$\mathrm{id} = \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n}),$$

and the proof that $i_\infty$ and $j_\infty$ are inverse to one another is complete. $\square$

We can explain the idea of this proof in other terms using a suggestion made to me by F. W. Lawvere. Consider the category of

We can explain the idea of this proof in other terms using a suggestion made to me by F. W. Lawvere. Consider the category of continuous lattices and projections. In that category our $D_\infty$ is, as we have remarked, both a *direct* and an *inverse* limit. Note too that with regard to projections $[D \to D']$ is a *functor*, for we can also define $[j \to j']$ when the maps are projections. In this language our particular inverse system is defined by the recursion:

$$D_{n+1} = [D_n \to D_n] \quad \text{and} \quad j_{n+1} = [j_n \to j_n],$$

where $D_0$ and $j_0$ are given in advance. Now the function space construction is continuous in its two arguments, turning an inverse limit on the right into an inverse limit and a direct limit on the *left* also into an *inverse* limit. A repeated limit can be made into a simple limit, so we can write:

$$
\begin{aligned}
D_\infty &= \varprojlim \langle D_n, j_n \rangle_{n=0}^{\infty} 
&= \varinjlim \langle D_n, i_n \rangle_{n=0}^{\infty}
\end{aligned}
$$

and

$$
\begin{aligned}
[D_\infty \to D_\infty] &= \varprojlim \langle [D_n \to D_n], [j_n \to j_n] \rangle_{n=0}^{\infty} 
&= \varprojlim \langle D_{n+1}, j_{n+1} \rangle_{n=0}^{\infty} 
&= D_\infty \quad \textit{(up to isomorphism).}
\end{aligned}
$$

A full checking of the details involved would not make the argument appreciably simpler over the more "element-by-element" argument I have presented. In fact, the proofs are actually the same. But thinking of the result in terms of properties of functors does seem to isolate very well the essential idea and to show how simple it is.

One must only add here a note of caution: the proper choice of category must be done with care. Thus it seems to me that the use of projections rather than arbitrary continuous maps is necessary.

Inasmuch as I have not checked all details in this form, I hope what I say is correct.

Since we have shown $[D_\infty \to D_\infty]$ to be homeomorphic to $D_\infty$, we can begin to regard them as the same. In particular there ought to be some function space structure to transfer to $D_\infty$. This can be done by defining functional application for any elements $x, y \in D_\infty$ by the equation:

$$x(y) = \bigsqcup_{n=0}^{\infty} i_{n\infty}(x_{n+1}(y_n)).$$

Similarly we can define $\lambda$-abstraction on continuous expressions:

$$\lambda x.[\ldots x \ldots] = j_\infty(\lambda x : D_\infty.[\ldots x \ldots]),$$

and in this way $D_\infty$ becomes a model for the $\lambda$-calculus of Church and Curry. The model-theoretic and proof-theoretic aspects of this result will be explained in another paper (Scott (1972)).

Suppose we were to start with the least, non-trivial lattice $0 = \top, \bot$ for $D_0$. Now $D_1 = [0 \to 0]$ has exactly three elements and there are just two ways of defining a projection $j_0 : D_1 \to D_0$. They are illustrated in the figure:

**Left projection**

```
      ⊤  ←── j₀ ──  [⊤,⊤]
      ⊥  ←── j₀ ──  [⊥,⊤]
      ⊥  ←── j₀ ──  [⊥,⊥]
```

**Right projection**

```
      ⊤  ←── j₀ ──  [⊤,⊤]
      ⊤  ←── j₀ ──  [⊥,⊤]
      ⊥  ←── j₀ ──  [⊥,⊥]
```

Hence our construction gives two limit spaces $D_\infty$ and $D'*\infty$. Are they the same? No, they are not. It can be shown, for example, that the $\top$ of $D*\infty$ is *isolated* (that is, $\top \ll \top$), while the same is not true of $D'*\infty$. More interestingly, David Park has proved that the fixed-point operator fix mentioned in 3.14 has algebraic properties in $D*\infty$ quite different from those in $D'*\infty$. By algebraic here, we of course have reference to the functional algebra embodied in the application operation $x(y)$ defined on these limit spaces. Note, by the way, that in view of our isomorphism result we can regard fix (or any other similar continuous function for that matter) as an element of $D*\infty$. This makes the "algebra" of $D_\infty$ quite a rich field for study.

The reader will have surely remarked that by virtue of 1.5, every $T_0$-space $X$ whatsoever can be embedded as a subspace in a $D_\infty$. Besides this all the continuous functions on $X$ (oh, into $D_\infty$, say) can be extended to $D_\infty$; whence they can be regarded as *elements* of $D_\infty$. Thus we have been able to embed not only the topology of $X$ into $D_\infty$ but also all of the continuous function theory over $X$. So far this is only a "logical" construction. For more interesting "mathematical" results we shall have to investigate whether any useful theorems about the usual function spaces $[X \to X]$ can be obtained with the aid of $D_\infty$. This method can easily be employed for real- or complex-valued continuous functions, though it seems more oriented toward pointwise convergence than anything else. Still, there seems to be a chance it might be useful—especially if one wished to consider continuous *operators* on function spaces.

The idea of forming the limit space can also be applied to *other* functors besides $[D \to D]$. Thus instead of solving the “equation”

$$D = [D \to D]$$

as we have done with the $D_\infty$ construction, we could also solve:

$$V = T + [V \times V] + [V + V] + [V \to V],$$

for example. Here $T = \bot, 0, 1, \top$ is the four-element lattice with $0$ and $1$ as incomparable elements. By $[V \times V]$ and $[V \to V]$ we understand the usual Cartesian product and function space construction. The $+$ operator, on the other hand works only in the category of lattices with $\top$ as an isolated element. It is defined so as to make:

$$
\begin{array}{ccc}
D + D' & \longleftarrow & D' 
\uparrow & & \uparrow 
D & \longleftarrow & 0
\end{array}
$$

a push-out diagram, where the maps from $0$ are meant to match $\bot$ with $\bot$ and $\top$ with $\top$. The point of requiring $\top$ to be isolated is that both $D$ and $D'$ become projections of $D + D'$. This construction, though not quite a disjoint union, has many properties in common with that operation on spaces. In particular, if we consider the category with projections as maps, the construction

$$\mathbb{F}(D) = T + [D \times D] + [D + D] + [D \to D]$$

is a *functor*. Furthermore, we can project $\mathbb{F}(T)$ onto $T$ in an obvious way, thereby setting things up for an inverse limit construction:

$$V = \varprojlim \langle \mathbb{F}^n(T), j_n \rangle_{n=0}^{\infty}.$$

The resulting continuous lattice satisfies the desired equation up to isomorphism.

The space $V$ constructed in the way just indicated is very rich in subspaces. To see this, consider the space $\mathcal{J}_V$ of proper projections $j$ where $j(\top) = \top$. As in 3.12 this is a complete lattice. Now that $[V \times V]$ and $[V + V]$ and $[V \to V]$ are regarded as *subspaces* of this “universe” $V$ itself, we can easily define *continuous operations*

$$(j \times k)\ ,\ (j + k)\ ,\ \text{and}\ (j \to k)$$

on the projections obtaining again elements of $\mathcal{J}_V$. The projections so obtained correspond to the indicated constructions of subspaces, of course. (Indeed, if we had the time and space, we could show that $\mathcal{J}_V$ becomes a very interesting category). There will be a particular

projection $t$ corresponding to $T$, and reason for doing all this is to show that the existence of subspaces of $V$ can now be established by solving equations in $\mathcal{J}_V$. For example, by the fixed-point construction we could find a $j \in \mathcal{J}_V$ such that

$$j = t + (t \times j) + ((j \times j) \to j).$$

The range of $j$ would then be a subspace $W \subseteq V$ such that $W$ solves the equation:

$$W = T + [T \times W] + [[W \times W] \to W].$$

And these are only a few examples: simultaneous equations are possible, and many other operators are waiting for discovery and application.

**Lean 4**

- [ContinuousLattice/FunctionSpaceTower.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower.lean)
- [ContinuousLattice/FunctionSpaceTower/Basic.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/Basic.lean)
- [ContinuousLattice/FunctionSpaceTower/BasicInst5.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/BasicInst5.lean)
- [ContinuousLattice/FunctionSpaceTower/BasicInst8.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/BasicInst8.lean)
- [ContinuousLattice/FunctionSpaceTower/CLat.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/CLat.lean)
- [ContinuousLattice/FunctionSpaceTower/DInf.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/DInf.lean)
- [ContinuousLattice/FunctionSpaceTower/DInfFn.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/DInfFn.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMap.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/conjMap.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMapFun.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/conjMapFun.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMapFun_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/conjMapFun_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMap_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/conjMap_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMap_iSup.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/conjMap_iSup.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMap_incl_le_conjMap_succ.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/conjMap_incl_le_conjMap_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMap_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/conjMap_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaceTower/conj_iInfTerm_eq.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/conj_iInfTerm_eq.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/embInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/embInfInf_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf_comp_projInfInf.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/embInfInf_comp_projInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf_le_iff.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/embInfInf_le_iff.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/embInfInf_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf_projInfInf.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/embInfInf_projInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/embInf_succ_iSup.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/embInf_succ_iSup.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceInclFun.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/functionSpaceInclFun.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceInclFun_continuous.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/functionSpaceInclFun_continuous.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceInclFun_outer_continuous.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/functionSpaceInclFun_outer_continuous.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceInclRetrLe.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/functionSpaceInclRetrLe.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceProjection.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/functionSpaceProjection.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceRetrFun.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/functionSpaceRetrFun.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceRetrFun_continuous.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/functionSpaceRetrFun_continuous.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceRetrFun_outer_continuous.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/functionSpaceRetrFun_outer_continuous.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceRetrIncl.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/functionSpaceRetrIncl.lean)
- [ContinuousLattice/FunctionSpaceTower/iInfTerm.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/iInfTerm.lean)
- [ContinuousLattice/FunctionSpaceTower/iInfTerm_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/iInfTerm_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/iInfTerm_le_succ.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/iInfTerm_le_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/iInfTerm_monotone.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/iInfTerm_monotone.lean)
- [ContinuousLattice/FunctionSpaceTower/iSup₂_monotone_eq_diagonal.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/iSup₂_monotone_eq_diagonal.lean)
- [ContinuousLattice/FunctionSpaceTower/incl_projInf_le_projInf_succ.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/incl_projInf_le_projInf_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/jInfTerm.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/jInfTerm.lean)
- [ContinuousLattice/FunctionSpaceTower/jInfTerm_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/jInfTerm_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/projInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/projInfInf_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf_comp_embInfInf.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/projInfInf_comp_embInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf_embInfInf.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/projInfInf_embInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf_embInfInf_eq.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/projInfInf_embInfInf_eq.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/projInfInf_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaceTower/theorem_4_4.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/theorem_4_4.lean)
- [ContinuousLattice/FunctionSpaceTower/theorem_4_4_inverses.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/theorem_4_4_inverses.lean)
- [ContinuousLattice/FunctionSpaceTower/theorem_4_4_orderIso.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/theorem_4_4_orderIso.lean)
- [ContinuousLattice/FunctionSpaceTower/theorem_4_4_scottTopology_homeomorph.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/theorem_4_4_scottTopology_homeomorph.lean)
- [ContinuousLattice/FunctionSpaceTower/theorem_4_4_sourceTopology_homeomorph.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/theorem_4_4_sourceTopology_homeomorph.lean)
- [ContinuousLattice/FunctionSpaceTower/towerCLat.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerCLat.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerProj.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj_incl_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerProj_incl_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj_retr_conjMap_succ.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerProj_retr_conjMap_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj_succ.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerProj_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj_succ_incl_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerProj_succ_incl_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj_succ_retr_apply.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerProj_succ_retr_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/towerToMap.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerToMap.lean)
- [ContinuousLattice/FunctionSpaceTower/towerToMap_coe.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerToMap_coe.lean)
- [ContinuousLattice/FunctionSpaceTower/towerType.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerType.lean)
- [ContinuousLattice/FunctionSpaceTower/towerType_succ.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerType_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/towerType_zero.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/towerType_zero.lean)
- [ContinuousLattice/InverseLimits.lean](DomainTheory/ContinuousLattice/InverseLimits.lean)
- [ContinuousLattice/InverseLimits/Basic.lean](DomainTheory/ContinuousLattice/InverseLimits/Basic.lean)
- [ContinuousLattice/InverseLimits/BasicInst20.lean](DomainTheory/ContinuousLattice/InverseLimits/BasicInst20.lean)
- [ContinuousLattice/InverseLimits/Compatible.lean](DomainTheory/ContinuousLattice/InverseLimits/Compatible.lean)
- [ContinuousLattice/InverseLimits/InverseLimit.lean](DomainTheory/ContinuousLattice/InverseLimits/InverseLimit.lean)
- [ContinuousLattice/InverseLimits/coconeInf.lean](DomainTheory/ContinuousLattice/InverseLimits/coconeInf.lean)
- [ContinuousLattice/InverseLimits/coconeInf_apply.lean](DomainTheory/ContinuousLattice/InverseLimits/coconeInf_apply.lean)
- [ContinuousLattice/InverseLimits/coconeInf_climb.lean](DomainTheory/ContinuousLattice/InverseLimits/coconeInf_climb.lean)
- [ContinuousLattice/InverseLimits/coconeInf_comp_embInf.lean](DomainTheory/ContinuousLattice/InverseLimits/coconeInf_comp_embInf.lean)
- [ContinuousLattice/InverseLimits/coconeInf_descend.lean](DomainTheory/ContinuousLattice/InverseLimits/coconeInf_descend.lean)
- [ContinuousLattice/InverseLimits/coconeInf_inverseLimitTopology_continuous.lean](DomainTheory/ContinuousLattice/InverseLimits/coconeInf_inverseLimitTopology_continuous.lean)
- [ContinuousLattice/InverseLimits/coconeInf_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/InverseLimits/coconeInf_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/coe_sInf.lean](DomainTheory/ContinuousLattice/InverseLimits/coe_sInf.lean)
- [ContinuousLattice/InverseLimits/coe_sSup_of_directed.lean](DomainTheory/ContinuousLattice/InverseLimits/coe_sSup_of_directed.lean)
- [ContinuousLattice/InverseLimits/compatible_sInf.lean](DomainTheory/ContinuousLattice/InverseLimits/compatible_sInf.lean)
- [ContinuousLattice/InverseLimits/corollary_4_3.lean](DomainTheory/ContinuousLattice/InverseLimits/corollary_4_3.lean)
- [ContinuousLattice/InverseLimits/embInf.lean](DomainTheory/ContinuousLattice/InverseLimits/embInf.lean)
- [ContinuousLattice/InverseLimits/embInfFun.lean](DomainTheory/ContinuousLattice/InverseLimits/embInfFun.lean)
- [ContinuousLattice/InverseLimits/embInfFun_coe.lean](DomainTheory/ContinuousLattice/InverseLimits/embInfFun_coe.lean)
- [ContinuousLattice/InverseLimits/embInf_family_directed.lean](DomainTheory/ContinuousLattice/InverseLimits/embInf_family_directed.lean)
- [ContinuousLattice/InverseLimits/embInf_inverseLimitTopology_continuous.lean](DomainTheory/ContinuousLattice/InverseLimits/embInf_inverseLimitTopology_continuous.lean)
- [ContinuousLattice/InverseLimits/embInf_le_succ.lean](DomainTheory/ContinuousLattice/InverseLimits/embInf_le_succ.lean)
- [ContinuousLattice/InverseLimits/embInf_monotone.lean](DomainTheory/ContinuousLattice/InverseLimits/embInf_monotone.lean)
- [ContinuousLattice/InverseLimits/embInf_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/InverseLimits/embInf_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/embInf_succ.lean](DomainTheory/ContinuousLattice/InverseLimits/embInf_succ.lean)
- [ContinuousLattice/InverseLimits/embLE.lean](DomainTheory/ContinuousLattice/InverseLimits/embLE.lean)
- [ContinuousLattice/InverseLimits/embLE_le.lean](DomainTheory/ContinuousLattice/InverseLimits/embLE_le.lean)
- [ContinuousLattice/InverseLimits/embLE_mono.lean](DomainTheory/ContinuousLattice/InverseLimits/embLE_mono.lean)
- [ContinuousLattice/InverseLimits/embLE_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/InverseLimits/embLE_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/embLE_self.lean](DomainTheory/ContinuousLattice/InverseLimits/embLE_self.lean)
- [ContinuousLattice/InverseLimits/embLE_succ.lean](DomainTheory/ContinuousLattice/InverseLimits/embLE_succ.lean)
- [ContinuousLattice/InverseLimits/embLE_succ_left.lean](DomainTheory/ContinuousLattice/InverseLimits/embLE_succ_left.lean)
- [ContinuousLattice/InverseLimits/eval_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/InverseLimits/eval_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/iComp.lean](DomainTheory/ContinuousLattice/InverseLimits/iComp.lean)
- [ContinuousLattice/InverseLimits/iComp_compatible.lean](DomainTheory/ContinuousLattice/InverseLimits/iComp_compatible.lean)
- [ContinuousLattice/InverseLimits/iComp_incl_le.lean](DomainTheory/ContinuousLattice/InverseLimits/iComp_incl_le.lean)
- [ContinuousLattice/InverseLimits/iComp_monotone.lean](DomainTheory/ContinuousLattice/InverseLimits/iComp_monotone.lean)
- [ContinuousLattice/InverseLimits/iComp_of_ge.lean](DomainTheory/ContinuousLattice/InverseLimits/iComp_of_ge.lean)
- [ContinuousLattice/InverseLimits/iComp_of_le.lean](DomainTheory/ContinuousLattice/InverseLimits/iComp_of_le.lean)
- [ContinuousLattice/InverseLimits/iComp_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/InverseLimits/iComp_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/iComp_self.lean](DomainTheory/ContinuousLattice/InverseLimits/iComp_self.lean)
- [ContinuousLattice/InverseLimits/idInf_eq_iSup.lean](DomainTheory/ContinuousLattice/InverseLimits/idInf_eq_iSup.lean)
- [ContinuousLattice/InverseLimits/instCompleteLattice.lean](DomainTheory/ContinuousLattice/InverseLimits/instCompleteLattice.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLE.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimitLE.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLE_antisymm.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimitLE_antisymm.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLE_refl.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimitLE_refl.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLE_trans.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimitLE_trans.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLT.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimitLT.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLT_iff_LE_not_GE.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimitLT_iff_LE_not_GE.lean)
- [ContinuousLattice/InverseLimits/inverseLimitPartialOrder.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimitPartialOrder.lean)
- [ContinuousLattice/InverseLimits/inverseLimitSInfCoe.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimitSInfCoe.lean)
- [ContinuousLattice/InverseLimits/inverseLimitTopology.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimitTopology.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_coordinate_continuous.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimit_coordinate_continuous.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_eq_iSup.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimit_eq_iSup.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_isInjectiveSpace.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimit_isInjectiveSpace.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_scottTopology_eq_induced_pi.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimit_scottTopology_eq_induced_pi.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_specializationLe_iff.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimit_specializationLe_iff.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_t0Space.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimit_t0Space.lean)
- [ContinuousLattice/InverseLimits/isGLB_sInf'.lean](DomainTheory/ContinuousLattice/InverseLimits/isGLB_sInf'.lean)
- [ContinuousLattice/InverseLimits/lemma_4_5.lean](DomainTheory/ContinuousLattice/InverseLimits/lemma_4_5.lean)
- [ContinuousLattice/InverseLimits/projInf.lean](DomainTheory/ContinuousLattice/InverseLimits/projInf.lean)
- [ContinuousLattice/InverseLimits/projInfFun.lean](DomainTheory/ContinuousLattice/InverseLimits/projInfFun.lean)
- [ContinuousLattice/InverseLimits/projInf_inverseLimitTopology_continuous.lean](DomainTheory/ContinuousLattice/InverseLimits/projInf_inverseLimitTopology_continuous.lean)
- [ContinuousLattice/InverseLimits/projLE.lean](DomainTheory/ContinuousLattice/InverseLimits/projLE.lean)
- [ContinuousLattice/InverseLimits/projLE_compatible.lean](DomainTheory/ContinuousLattice/InverseLimits/projLE_compatible.lean)
- [ContinuousLattice/InverseLimits/projLE_mono.lean](DomainTheory/ContinuousLattice/InverseLimits/projLE_mono.lean)
- [ContinuousLattice/InverseLimits/projLE_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/InverseLimits/projLE_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/projLE_retr.lean](DomainTheory/ContinuousLattice/InverseLimits/projLE_retr.lean)
- [ContinuousLattice/InverseLimits/projLE_self.lean](DomainTheory/ContinuousLattice/InverseLimits/projLE_self.lean)
- [ContinuousLattice/InverseLimits/projLE_succ.lean](DomainTheory/ContinuousLattice/InverseLimits/projLE_succ.lean)
- [ContinuousLattice/InverseLimits/projection_galoisConnection.lean](DomainTheory/ContinuousLattice/InverseLimits/projection_galoisConnection.lean)
- [ContinuousLattice/InverseLimits/proposition_4_1.lean](DomainTheory/ContinuousLattice/InverseLimits/proposition_4_1.lean)
- [ContinuousLattice/InverseLimits/proposition_4_2.lean](DomainTheory/ContinuousLattice/InverseLimits/proposition_4_2.lean)
- [ContinuousLattice/InverseLimits/retr_sInf.lean](DomainTheory/ContinuousLattice/InverseLimits/retr_sInf.lean)
