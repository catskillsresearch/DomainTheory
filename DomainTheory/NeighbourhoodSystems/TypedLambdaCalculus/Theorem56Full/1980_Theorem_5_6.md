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

- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/T_bot_eq.lean](../Theorem56/T_bot_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/kSel.lean](../Theorem56/kSel.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muBody_apply.lean](../Theorem56/muBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muMap_natElem.lean](../Theorem56/muMap_natElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_rec.lean](../Theorem56/muRec_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_bot.lean](../Theorem56/muRec_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_found.lean](../Theorem56/muRec_found.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_step.lean](../Theorem56/muRec_step.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec_climb.lean](../Theorem56/muRec_climb.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muMap_eq_least.lean](../Theorem56/muMap_eq_least.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56.lean](../Theorem56.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primBody_apply.lean](../Theorem56/primBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_rec.lean](../Theorem56/primRec_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_bot.lean](../Theorem56/primRec_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_succ.lean](../Theorem56/primRec_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec_zero.lean](../Theorem56/primRec_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/qSel.lean](../Theorem56/qSel.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/argX.lean](../Theorem56/argX.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/argY.lean](../Theorem56/argY.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muBody.lean](../Theorem56/muBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muOp.lean](../Theorem56/muOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muRec.lean](../Theorem56/muRec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/muMap.lean](../Theorem56/muMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primBody.lean](../Theorem56/primBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primOp.lean](../Theorem56/primOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/primRec.lean](../Theorem56/primRec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictId.lean](../Theorem56/strictId.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictId_bot.lean](../Theorem56/strictId_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictId_natElem.lean](../Theorem56/strictId_natElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_apply.lean](../Theorem56/strictProju2080_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_bot_left.lean](../Theorem56/strictProju2080_bot_left.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_bot_right.lean](../Theorem56/strictProju2080_bot_right.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProju2080_natElem.lean](../Theorem56/strictProju2080_natElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/strictProj₀.lean](../Theorem56/strictProj₀.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem56/Basic.lean](../Theorem56/Basic.lean)
