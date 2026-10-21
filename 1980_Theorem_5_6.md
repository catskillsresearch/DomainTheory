# Theorem 5.6

The reader will have noted that there are some combinators not appearing in Table 5.5. The reason is that combinators like $\mathrm{cond}$, $\mathrm{succ}$, $\mathrm{pred}$, $\mathrm{zero}$, $0$ cannot be defined in the pure $\lambda$-notation but are specific to domains like $T$ and $\mathbf{N}$; we, thus, have to regard them as primitive. But once they are in hand, a very large number of other functions can be defined from these combined with $\lambda$-expressions. The next theorem gives an indication of the possibilities.

**THEOREM 5.6.** For every partial recursive function $h : \mathbf{N} \to \mathbf{N}$, there is a $\lambda$-term $\tau$ of type $(\mathbf{N} \to \mathbf{N})$ such that the only constants occurring in $\tau$ are

$$
\mathrm{cond},\ \mathrm{succ},\ \mathrm{pred},\ \mathrm{zero},\ 0
$$

and where if $h(n) = m$, then

$$
\tau(n) = m
$$
is true; and if $h(n)$ is undefined, then

$$
\tau(n) = \bot
$$

is true. The equation $\tau(\bot) = \bot$ is also true.

*Proof :* We have only formulated the theorem for functions of one variable — but to give the proof, it is convenient to pass through functions of any number of (integer) variables. We shall also have to recall the precise definition of the notion of partial recursive function.

It is also convenient to work with (*very*)*strict* functions

$$
f : \mathbf{N}^k \to \mathbf{N}.
$$

These are functions such that if $n_0, \ldots, n_{k-1} \in \mathbf{N}$ and $n_i = \bot$ for at least one $i < k$, then

$$
f(n_0, \ldots, n_{k-1}) = \bot.
$$

It is easy to check that compositions of strict functions are strict. It is also easy to see that any *partial* function

$$
g : \mathbf{N}^k \to \mathbf{N}
$$

extends to a strict (*approximable*) function

$$
\bar{g} : \mathbf{N}^k \to \mathbf{N},
$$

which takes the same values as $g$ as long as $g$ is defined; otherwise $\bar{g}$ takes the value $\bot$. What we want to show for *partial recursive* $g$ is that the corresponding $\bar{g}$ is defined by a $\lambda$ - expression.

In the first place we have to check that *primitive recursive* functions have $\lambda$ - definitions in this sense. We recall that *primitive recursive* functions are generated from certain elementary *starting* functions by multi-variate composition and the scheme of primitive recrusion. The *starting* functions are the constant function with value zero and the "identity" or "projection" functions. For example, $g(n_0, n_1, n_2) = n_1$ for all $n_0, n_1, n_2 \in \mathbf{N}$ is one of the *starting* functions. Now we cannot just use the $\lambda$-term

$$
\lambda x_0, x_1, x_2 . x_1
$$

to represent $\bar{g}$, because the function so defined is not strict. But any function in $\mathbf{N}^k \to \mathbf{N}$ can be cut down to a strict function by a simple device. Consider
$$
\lambda x.\ \mathrm{cond}(\mathrm{zero}(x), x, x)
$$

with $x$ of type $\mathbf{N}$. This is the strict version of the identity function of one argument. The strict projection function of two arguments can be defined by

$$
\lambda x_0, x_1.\ \mathrm{cond}(\mathrm{zero}(x_1), x_0, x_0).
$$

The one of three arguments by:

$$
\lambda x_0, x_1, x_2.\ \mathrm{cond}(\mathrm{zero}(x_0), \mathrm{cond}(\mathrm{zero}(x_2), x_1, x_1), \mathrm{cond}(\mathrm{zero}(x_2), x_1, x_1)).
$$

This is not done very elegantly, and the reader can find for himself a general solution based on perhaps a better notation for the required compositions of functions.

As we remarked, strict functions are closed under substitution, and any substitution of a batch of functions into another function can be given by a $\lambda$-term, if the various functions can themselves be so defined. It only remains to $\lambda$-define functions obtained by primitive recursion. Thus, suppose, for the sake of argument, that

$$
\bar{f} : \mathbf{N} \to \mathbf{N} \qquad \text{and} \qquad \bar{g} : \mathbf{N}^3 \to \mathbf{N}
$$

are given as total functions with $\bar{f}$ and $\bar{g}$ being $\lambda$-definable. From them, we obtain by primitive recursion $\bar{h} : \mathbf{N}^2 \to \mathbf{N}$ where

$$
\bar{h}(0, m) = \bar{f}(m),
$$

$$
\bar{h}(n+1, m) = \bar{g}(n, m, \bar{h}(n, m))
$$

for all $n, m \in \mathbf{N}$. The $\lambda$-term defining $\bar{h}$ is

$$
!k\ \lambda x, y.\ \mathrm{cond}(\mathrm{zero}(x), \bar{f}(y), \bar{g}(\mathrm{pred}(x), y, k(\mathrm{pred}(x), y))).
$$

Here we have had to use the fixed-point operator on a variable $k$ of type $(\mathbf{N}^2 \to \mathbf{N})$. The variables $x, y$ are of type $\mathbf{N}$ and the $\mathrm{cond}$-construction puts the two traditional equations into two clauses of one expression. It is easy to see that the fixed-point function *is* strict and is nothing more than $\bar{h}$.

That completes the representation of *primitive recursive* functions. To obtain the *partial recursive* functions, the idea is to use the so-called $\mu$-scheme (least number operator) and, further, to close up under substitution. We need only treat the $\mu$-scheme. Suppose, by way of example, $f(n, m)$ is given as a
primitive recursive function. We then define $h$ (generally, a partial function) by

$$h(m) = \text{the least } n \text{ where } f(n,m) = 0.$$

This is often written

$$h(m) = \mu n.\, f(n,m) = 0.$$

Supposing, as we may, $\bar{f}$ is $\lambda$-definable, we introduce first

$$\bar{g} = !g\,\lambda x, y.\, \text{cond}(\text{zero}(\bar{f}(x,y)), x, g(\text{succ}(x), y)).$$

Then $\bar{h} = \lambda y.\, \bar{g}(0,y)$. This is easily seen to be strict. Also easy to see is that if $h(m)$ is defined, then $\bar{g}(0,m) = h(m)$. But, if $h(m)$ is not defined, it takes some argument to make sure that the least fixed-point construction forces $\bar{g}(0,m) = \bot$. However, the argument is not very difficult. $\square$

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/T_bot_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/T_bot_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/argX.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/argX.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/argY.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/argY.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/kSel.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/kSel.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muBody.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muBody_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muMap_eq_least.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muMap_eq_least.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muMap_natElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muMap_natElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muOp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_climb.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_climb.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_found.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_found.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_rec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_step.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_step.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primBody.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primBody_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primOp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_rec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/qSel.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/qSel.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictId.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictId.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictId_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictId_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictId_natElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictId_natElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_bot_left.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_bot_left.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_bot_right.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_bot_right.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_natElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_natElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProj₀.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProj₀.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/ArgLike.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/ArgLike.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/LamDef.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/LamDef.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/T_bot_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/T_bot_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/argElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/argElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/argElem_argLike.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/argElem_argLike.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_argElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_argElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_argElem_none.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_argElem_none.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_push_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_push_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_push_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_push_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_tupleMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_tupleMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_tupleMap_ge.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_tupleMap_ge.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_vecElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_vecElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_vecElem_lt.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/component_vecElem_lt.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/eq_of_component_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/eq_of_component_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/evalAt.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/evalAt.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/evalAt_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/evalAt_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findBody.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findBody_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findMap_vecElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findMap_vecElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findOp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findOp_iterElem_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/findOp_iterElem_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_inner_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_inner_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_total.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/guard1_total.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/iterVal_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/iterVal_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/iterVal_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/iterVal_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/iterVal_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/iterVal_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_coe_val.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_coe_val.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_comp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_comp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_congr.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_congr.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_get.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_get.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_of_inner.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_of_inner.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_prec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_prec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_primComp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_primComp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_rfind.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_rfind.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_total.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_total.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/lamDef_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/mem_mOfFn.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/mem_mOfFn.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/oneArg.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/oneArg.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/oneArg_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/oneArg_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/oneArg_natElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/oneArg_natElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/optElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/optElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/partrec_lamDef.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/partrec_lamDef.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/partrec_one.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/partrec_one.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/precBody.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/precBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/precBody_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/precBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/primrec_lamDef.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/primrec_lamDef.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/push_natElem_vecElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/push_natElem_vecElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/realizer_value.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/realizer_value.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recMap_eval.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recMap_eval.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recMap_rec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recMap_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recOp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/recOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/rfindZeroPred.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/rfindZeroPred.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_climb.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_climb.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_diverge.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_diverge.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_rec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_step_found.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_step_found.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_step_next.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/searchMap_step_next.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/strictGuardN.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/strictGuardN.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/strictGuardN_strict.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/strictGuardN_strict.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/strictGuardN_total.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/strictGuardN_total.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/toApproxMap_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/toApproxMap_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_argLike.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_argLike.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_vecElem_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_vecElem_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/tupleMap_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/vecElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/vecElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/vecElem_totals.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/vecElem_totals.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/𝒩.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem56Full/𝒩.lean)
