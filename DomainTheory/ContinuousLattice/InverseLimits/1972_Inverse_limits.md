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

- [Proposition 4.1](1972_Proposition_4_1.md)
- [Proposition 4.2](1972_Proposition_4_2.md)
- [Corollary 4.3](1972_Corollary_4_3.md)
- [Theorem 4.4](../FunctionSpaceTower/1972_Theorem_4_4.md)
- [Lemma 4.5](1972_Lemma_4_5.md)

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

- [ContinuousLattice/FunctionSpaceTower/CLat.lean](../FunctionSpaceTower/CLat.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMapFun_apply.lean](../FunctionSpaceTower/conjMapFun_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf_le_iff.lean](../FunctionSpaceTower/embInfInf_le_iff.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf_preservesDirectedSup.lean](../FunctionSpaceTower/embInfInf_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf_preservesDirectedSup.lean](../FunctionSpaceTower/projInfInf_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaceTower/towerCLat.lean](../FunctionSpaceTower/towerCLat.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj_succ.lean](../FunctionSpaceTower/towerProj_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj_succ_incl_apply.lean](../FunctionSpaceTower/towerProj_succ_incl_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj_incl_apply.lean](../FunctionSpaceTower/towerProj_incl_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/towerType.lean](../FunctionSpaceTower/towerType.lean)
- [ContinuousLattice/FunctionSpaceTower/BasicInst5.lean](../FunctionSpaceTower/BasicInst5.lean)
- [ContinuousLattice/FunctionSpaceTower/towerType_succ.lean](../FunctionSpaceTower/towerType_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/towerType_zero.lean](../FunctionSpaceTower/towerType_zero.lean)
- [ContinuousLattice/FunctionSpaceTower/towerToMap.lean](../FunctionSpaceTower/towerToMap.lean)
- [ContinuousLattice/FunctionSpaceTower/BasicInst8.lean](../FunctionSpaceTower/BasicInst8.lean)
- [ContinuousLattice/FunctionSpaceTower/towerToMap_coe.lean](../FunctionSpaceTower/towerToMap_coe.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMapFun.lean](../FunctionSpaceTower/conjMapFun.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMap_preservesDirectedSup.lean](../FunctionSpaceTower/conjMap_preservesDirectedSup.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMap.lean](../FunctionSpaceTower/conjMap.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMap_apply.lean](../FunctionSpaceTower/conjMap_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceInclFun_continuous.lean](../FunctionSpaceTower/functionSpaceInclFun_continuous.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceInclFun.lean](../FunctionSpaceTower/functionSpaceInclFun.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceInclFun_outer_continuous.lean](../FunctionSpaceTower/functionSpaceInclFun_outer_continuous.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceRetrFun_continuous.lean](../FunctionSpaceTower/functionSpaceRetrFun_continuous.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceRetrFun.lean](../FunctionSpaceTower/functionSpaceRetrFun.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceInclRetrLe.lean](../FunctionSpaceTower/functionSpaceInclRetrLe.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceRetrFun_outer_continuous.lean](../FunctionSpaceTower/functionSpaceRetrFun_outer_continuous.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceRetrIncl.lean](../FunctionSpaceTower/functionSpaceRetrIncl.lean)
- [ContinuousLattice/FunctionSpaceTower/functionSpaceProjection.lean](../FunctionSpaceTower/functionSpaceProjection.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj.lean](../FunctionSpaceTower/towerProj.lean)
- [ContinuousLattice/FunctionSpaceTower/DInf.lean](../FunctionSpaceTower/DInf.lean)
- [ContinuousLattice/FunctionSpaceTower/DInfFn.lean](../FunctionSpaceTower/DInfFn.lean)
- [ContinuousLattice/FunctionSpaceTower/iInfTerm.lean](../FunctionSpaceTower/iInfTerm.lean)
- [ContinuousLattice/FunctionSpaceTower/iInfTerm_apply.lean](../FunctionSpaceTower/iInfTerm_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf.lean](../FunctionSpaceTower/embInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf_apply.lean](../FunctionSpaceTower/embInfInf_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/jInfTerm.lean](../FunctionSpaceTower/jInfTerm.lean)
- [ContinuousLattice/FunctionSpaceTower/jInfTerm_apply.lean](../FunctionSpaceTower/jInfTerm_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMap_iSup.lean](../FunctionSpaceTower/conjMap_iSup.lean)
- [ContinuousLattice/FunctionSpaceTower/conj_iInfTerm_eq.lean](../FunctionSpaceTower/conj_iInfTerm_eq.lean)
- [ContinuousLattice/FunctionSpaceTower/embInf_succ_iSup.lean](../FunctionSpaceTower/embInf_succ_iSup.lean)
- [ContinuousLattice/FunctionSpaceTower/iSup₂_monotone_eq_diagonal.lean](../FunctionSpaceTower/iSup₂_monotone_eq_diagonal.lean)
- [ContinuousLattice/FunctionSpaceTower/incl_projInf_le_projInf_succ.lean](../FunctionSpaceTower/incl_projInf_le_projInf_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/conjMap_incl_le_conjMap_succ.lean](../FunctionSpaceTower/conjMap_incl_le_conjMap_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf.lean](../FunctionSpaceTower/projInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf_apply.lean](../FunctionSpaceTower/projInfInf_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj_retr_conjMap_succ.lean](../FunctionSpaceTower/towerProj_retr_conjMap_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf_comp_projInfInf.lean](../FunctionSpaceTower/embInfInf_comp_projInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/embInfInf_projInfInf.lean](../FunctionSpaceTower/embInfInf_projInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/towerProj_succ_retr_apply.lean](../FunctionSpaceTower/towerProj_succ_retr_apply.lean)
- [ContinuousLattice/FunctionSpaceTower/iInfTerm_le_succ.lean](../FunctionSpaceTower/iInfTerm_le_succ.lean)
- [ContinuousLattice/FunctionSpaceTower/iInfTerm_monotone.lean](../FunctionSpaceTower/iInfTerm_monotone.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf_embInfInf_eq.lean](../FunctionSpaceTower/projInfInf_embInfInf_eq.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf_comp_embInfInf.lean](../FunctionSpaceTower/projInfInf_comp_embInfInf.lean)
- [ContinuousLattice/FunctionSpaceTower/projInfInf_embInfInf.lean](../FunctionSpaceTower/projInfInf_embInfInf.lean)
- [ContinuousLattice/InverseLimits/Compatible.lean](Compatible.lean)
- [ContinuousLattice/InverseLimits/InverseLimit.lean](InverseLimit.lean)
- [ContinuousLattice/InverseLimits/coconeInf_apply.lean](coconeInf_apply.lean)
- [ContinuousLattice/InverseLimits/coconeInf_climb.lean](coconeInf_climb.lean)
- [ContinuousLattice/InverseLimits/coconeInf_descend.lean](coconeInf_descend.lean)
- [ContinuousLattice/InverseLimits/coconeInf_comp_embInf.lean](coconeInf_comp_embInf.lean)
- [ContinuousLattice/InverseLimits/coconeInf_preservesDirectedSup.lean](coconeInf_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/coe_sInf.lean](coe_sInf.lean)
- [ContinuousLattice/InverseLimits/embLE_mono.lean](embLE_mono.lean)
- [ContinuousLattice/InverseLimits/embLE_succ_left.lean](embLE_succ_left.lean)
- [ContinuousLattice/InverseLimits/embInf_succ.lean](embInf_succ.lean)
- [ContinuousLattice/InverseLimits/embInf_le_succ.lean](embInf_le_succ.lean)
- [ContinuousLattice/InverseLimits/embInf_family_directed.lean](embInf_family_directed.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLE.lean](inverseLimitLE.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLE_antisymm.lean](inverseLimitLE_antisymm.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLE_refl.lean](inverseLimitLE_refl.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLE_trans.lean](inverseLimitLE_trans.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLT.lean](inverseLimitLT.lean)
- [ContinuousLattice/InverseLimits/inverseLimitLT_iff_LE_not_GE.lean](inverseLimitLT_iff_LE_not_GE.lean)
- [ContinuousLattice/InverseLimits/inverseLimitPartialOrder.lean](inverseLimitPartialOrder.lean)
- [ContinuousLattice/InverseLimits/inverseLimitSInfCoe.lean](inverseLimitSInfCoe.lean)
- [ContinuousLattice/InverseLimits/inverseLimitTopology.lean](inverseLimitTopology.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_coordinate_continuous.lean](inverseLimit_coordinate_continuous.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_eq_iSup.lean](inverseLimit_eq_iSup.lean)
- [ContinuousLattice/InverseLimits/idInf_eq_iSup.lean](idInf_eq_iSup.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_isInjectiveSpace.lean](inverseLimit_isInjectiveSpace.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_specializationLe_iff.lean](inverseLimit_specializationLe_iff.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_t0Space.lean](inverseLimit_t0Space.lean)
- [ContinuousLattice/InverseLimits/inverseLimit_scottTopology_eq_induced_pi.lean](inverseLimit_scottTopology_eq_induced_pi.lean)
- [ContinuousLattice/InverseLimits/coconeInf_inverseLimitTopology_continuous.lean](coconeInf_inverseLimitTopology_continuous.lean)
- [ContinuousLattice/InverseLimits/embInf_inverseLimitTopology_continuous.lean](embInf_inverseLimitTopology_continuous.lean)
- [ContinuousLattice/InverseLimits/projInf_inverseLimitTopology_continuous.lean](projInf_inverseLimitTopology_continuous.lean)
- [ContinuousLattice/InverseLimits/projLE_mono.lean](projLE_mono.lean)
- [ContinuousLattice/InverseLimits/projection_galoisConnection.lean](projection_galoisConnection.lean)
- [ContinuousLattice/InverseLimits/retr_sInf.lean](retr_sInf.lean)
- [ContinuousLattice/InverseLimits/compatible_sInf.lean](compatible_sInf.lean)
- [ContinuousLattice/InverseLimits/BasicInst20.lean](BasicInst20.lean)
- [ContinuousLattice/InverseLimits/isGLB_sInf'.lean](isGLB_sInf'.lean)
- [ContinuousLattice/InverseLimits/instCompleteLattice.lean](instCompleteLattice.lean)
- [ContinuousLattice/InverseLimits/coe_sSup_of_directed.lean](coe_sSup_of_directed.lean)
- [ContinuousLattice/InverseLimits/embLE.lean](embLE.lean)
- [ContinuousLattice/InverseLimits/embLE_self.lean](embLE_self.lean)
- [ContinuousLattice/InverseLimits/embLE_succ.lean](embLE_succ.lean)
- [ContinuousLattice/InverseLimits/embLE_le.lean](embLE_le.lean)
- [ContinuousLattice/InverseLimits/embLE_preservesDirectedSup.lean](embLE_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/projLE.lean](projLE.lean)
- [ContinuousLattice/InverseLimits/iComp.lean](iComp.lean)
- [ContinuousLattice/InverseLimits/iComp_of_ge.lean](iComp_of_ge.lean)
- [ContinuousLattice/InverseLimits/iComp_of_le.lean](iComp_of_le.lean)
- [ContinuousLattice/InverseLimits/iComp_self.lean](iComp_self.lean)
- [ContinuousLattice/InverseLimits/projLE_self.lean](projLE_self.lean)
- [ContinuousLattice/InverseLimits/projLE_succ.lean](projLE_succ.lean)
- [ContinuousLattice/InverseLimits/projLE_compatible.lean](projLE_compatible.lean)
- [ContinuousLattice/InverseLimits/iComp_incl_le.lean](iComp_incl_le.lean)
- [ContinuousLattice/InverseLimits/projLE_preservesDirectedSup.lean](projLE_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/iComp_preservesDirectedSup.lean](iComp_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/iComp_monotone.lean](iComp_monotone.lean)
- [ContinuousLattice/InverseLimits/projLE_retr.lean](projLE_retr.lean)
- [ContinuousLattice/InverseLimits/iComp_compatible.lean](iComp_compatible.lean)
- [ContinuousLattice/InverseLimits/embInfFun.lean](embInfFun.lean)
- [ContinuousLattice/InverseLimits/embInfFun_coe.lean](embInfFun_coe.lean)
- [ContinuousLattice/InverseLimits/coconeInf.lean](coconeInf.lean)
- [ContinuousLattice/InverseLimits/embInf_monotone.lean](embInf_monotone.lean)
- [ContinuousLattice/InverseLimits/embInf_preservesDirectedSup.lean](embInf_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/embInf.lean](embInf.lean)
- [ContinuousLattice/InverseLimits/projInfFun.lean](projInfFun.lean)
- [ContinuousLattice/InverseLimits/eval_preservesDirectedSup.lean](eval_preservesDirectedSup.lean)
- [ContinuousLattice/InverseLimits/projInf.lean](projInf.lean)
