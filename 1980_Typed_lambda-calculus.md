# Typed $\lambda$-calculus

In Examples 4.3 and 4.4, after suitable domains have been constructed, functions are characterized by recursion equations whose form of expression is — basically — a composition or substitution of known functions together with the function to be defined. This method can be made more precise and more easily usable by expanding our notation for functions — particularly by inventing a "temporary" notation for a function as a thing in itself without having to have special letters for functions. The device is called *$\lambda$-abstraction*. It is related to ordinary set abstraction (the $\{x \mid \ldots\}$ — notation already much used in these lectures), but we gear the approach to domains and their elements, and especially to function spaces.

At this stage it would not be so helpful to produce a rigorously formal definition of the syntax of the typed $\lambda$-calculus; we shall try to suggest what is needed by example. There are so many examples at hand, the less formal discussion ought to be sufficient.

In the first place we should set aside, in the notational store room as it were, a stock of variables

$$
x, y, z, w, \ldots
$$

These variables will be required in different "sizes" or "types". Roughly speaking there should be an infinite number of variables to range over the elements of <u>each domain $\mathcal{D}$</u>. We could perhaps write

$$
x_0^{\mathcal{D}}, x_1^{\mathcal{D}}, x_2^{\mathcal{D}}, \ldots,
$$

but the subscripts to insure an infinity of variables and the superscripts to record the typing of the variables lead to a notation as
tiresome to write as it is to read. We simply agree that we can have as many variables as we need and that they come in all the types.

Strictly speaking we should also introduce *type symbols* and not confuse types with domains. But if the reader will simply keep in mind that *form* in language has always to be kept distinct from *content*, the confusion at the type level will not matter so very much. A point at which the confusion might cause a real confusion concerns *compound types*. Given $\mathcal{D}_0$ and $\mathcal{D}_1$ we can form such compounds as

$$
\mathcal{D}_0 + \mathcal{D}_1, \quad \mathcal{D}_0 \times \mathcal{D}_1, \quad \mathcal{D}_0 \to \mathcal{D}_1
$$

What has to be remembered is that a compound domain (neighbourhood system), $\mathcal{D}_0 \times \mathcal{D}_1$ say, does not uniquely determine the "parts" $\mathcal{D}_0$ and $\mathcal{D}_1$. (We could make it do so, but it would cost some effort.) Of course, the symbol "$\mathcal{D}_0 \times \mathcal{D}_1$" has well defined parts. The point is that *different* ways of forming a compound domain could lead to the *same* result, meaning that a domain does not let us retrace its exact history of construction. Compound symbols, however, always carry their histories around with them, since otherwise they would not be readable. What we want, of course, are *both* domain symbols *and* domains, the latter being the *meanings* of the former. Most of the time we can happily pretend that it is only the domains themselves we have to think about.

Besides variables, we will also need certain *constants*. For instance, the symbol $0$ (perhaps, better $0^{\mathbf{N}}$) denotes a certain element of $|\mathbf{N}|$. Similarly, in view of Theorem 4.2, for each domain $\mathcal{D}$ there is a well-determined element $\mathrm{fix}^{\mathcal{D}}$ of the compound type $((\mathcal{D} \to \mathcal{D}) \to \mathcal{D})$ denoting the least fixed-point operator. We have considered any number of similar constants of a great variety of types already (cf. 4.3 and 4.4; cond is an especially good one). We can say that the variables and constants are *atomic terms*, where "atomic" here means non-compound.

To form compound terms, there are several means: for example, if $\tau, \ldots, \sigma$ is a list of already obtained terms (including variables or constants), then we can form an ordered *tuple*
We have already done so in 3.1. If the types of $\tau, \dots, \sigma$ are $D, \dots, D'$, respectively, then the type of the tuple is the product domain

$$D \times \dots \times D',$$

because we intend that the tuple denote an element of this domain. (The tuple notation for *functions* as in 3.3 is being forgotten for the time being.)

Next suppose that $\tau$ has type $(D_0 \to D_1)$ and $\sigma$ has type $D_0$, then the usual *function-value* notation

$$\tau(\sigma)$$

is a compound term of type $D_1$. We also use

$$\tau(\sigma_0, \dots, \sigma_{n-1})$$

as an abbreviation of

$$\tau(\langle \sigma_0, \dots, \sigma_{n-1} \rangle),$$

where, if the types of $\sigma_0, \dots, \sigma_{n-1}$ are $D_0, \dots, D_{n-1}$, then the type of $\tau$ has to be of the form

$$((D_0 \times \dots \times D_{n-1}) \to D_n)$$

where $D_n$ is the type of the compound. In this manner, with functions applied to tuples, we have the full facility of substitution into functions of many variables just by iterating the notation.

Having taken into account *function value*, it remains to provide for *function definition*. Suppose that $x_0, \dots, x_{n-1}$ is a list of distinct variables of types $D_0, \dots, D_{n-1}$. Suppose further that $\tau$ is a term — no matter how complicated — of type $D_n$. Then we can regard $\tau$ as defining a function of $n$-variables of type

$$((D_0 \times \dots \times D_{n-1}) \to D_n).$$

What we have not done is to reward our regard by, as yet, providing a quick-to-write "name" for that function. This we now do; it is called

$$\lambda x_0, \dots, x_{n-1} \cdot \tau,$$

where we stress that the $x_i$ must be *distinct* variables and that this
expression denotes the *whole function*. That is why we provide it with a special symbol.

Here is an example of the $\lambda$ - notation

$$
\lambda x, y . x ,
$$

which is read "lambda ex wye ... (pause) ... ex". If the types of $x$ and $y$ are $D_0$ and $D_1$, then the type of the above is

$$
((D_0 \times D_1) \to D_0).
$$

Indeed, we know this function very well: it is the *first projection function* $p_0$ of 3.3 and the equation

$$
p_0 = \lambda x, y . x
$$

is true, as is the equation

$$
p_1 = \lambda x, y . y .
$$

In the notation of 3.3, we also find the true equation

$$
\langle f, g \rangle = \lambda w . \langle f(w), g(w) \rangle ,
$$

where on the right-hand side we are using "official" $\lambda$ - notation for a function of type

$$
(D_2 \to (D_0 \times D_1)).
$$

The notation on the left is just an *abbreviation* and it should not be confused with the pair (2-tuple) of type

$$
((D_2 \to D_0) \times (D_2 \to D_1)).
$$

(Since the two domains just mentioned are *isomorphic*, the possible confusion is not all that serious. On the other hand, one confusion we will completely overlook is that between 1-tuples $\langle x \rangle$ and elements $x$. Strictly speaking they are different, but we shall not bother to make the distinction.)

Here are some other examples of true equations:

$$
\mathrm{eval} = \lambda f, x . f(x) \qquad \text{(cf.\ 3.11)}
$$

$$
\mathrm{curry} = \lambda g \lambda x \lambda y . g(x, y) \qquad \text{(cf.\ 3.12)}
$$

The first should be immediately clear; while the second is particularly *instructive*. What is being illustrated is that the $\lambda$ - notation can
be *iterated*. The distinction being drawn is between

$$
\lambda x_0, x_1, \dots, x_{n-1} . \tau \quad \text{and} \quad \lambda x_0 \lambda x_1 \dots \lambda x_{n-1} . \tau .
$$

The first has type

$$
((D_0 \times D_1 \times \dots \times D_{n-1}) \to D_n);
$$

while the second has type

$$
(D_0 \to (D_1 \to (\dots (D_{n-1} \to D_n) \dots))).
$$

This is related also to the true equation

$$
\mathrm{curry} (\lambda x, y . \tau) = \lambda x \lambda y . \tau ,
$$

which shows that there are operators relating to the two notations. The first is the *multivariate* form; the second is the *curried* form.

Here is another true equation

$$
\mathrm{fix} = \mathrm{fix} (\lambda F \lambda f . f(F(f))),
$$

where the fix on the left has type $((D \to D) \to D)$ and that on the right type

$$
((((D \to D) \to D) \to ((D \to D) \to D)) \to ((D \to D) \to D)).
$$

This is the content of Exercise 4.9. (This also shows why type superscripts are tiresome.)

The combination

$$
\mathrm{fix} (\lambda x . \tau)
$$

occurs so often, that from time to time we abbreviate it as

$$
! x . \tau ,
$$

but remember it only makes sense if $x$ and $\tau$ have the *same* type. For example in 4.3 we could have written

$$
\sigma = ! f \lambda n . \mathrm{cond} (\mathrm{zero}(n), 0, f(\mathrm{pred}(n)) + \mathrm{pred}(n))
$$

and read this as

> "$\sigma$ is the least (recursively defined) function $f$ whose value at $n$ is cond $(\dots)$."

We note that in the so-called "body" of the expression inside the
cond-part the variable $f$ occurs again. That is just the point! This is a *recursive definition*; it is made into an *explicit* definition by invoking the least fixed-point operator.

In a $\lambda$-expression, $\lambda x, y, z . \tau$, say, the variables $x, y, z$ are being *bound* in $\tau$; but $\tau$ may have other variables that are nowhere bound in $\tau$ and these remain *free variables* of the whole expression. Bound variables are *dummy variables* and may be rewritten by other variables; thus

$$\lambda x . \tau = \lambda y . \tau [ y / x ]$$

is a true equation *PROVIDED* the variable $y$ does not occur in $\tau$. In the equation the notation $\tau [ y / x ]$ means the result of *substituting* (*rewriting*) the variable $y$ for the variable $x$ throughout the term $\tau$. We can also write $\tau [ \sigma / x ]$ for substituting a whole term $\sigma$ for a variable in the other term.

We have already spoken of "true equations", but how do we know that these curious equations are meaningful at all? They are, but this is something that has to be proved.

- [Theorem 5.1](1980_Theorem_5_1.md)
- [Theorem 5.2](1980_Theorem_5_2.md)
- [Proposition 5.3](1980_Proposition_5_3.md)
- [Proposition 5.4](1980_Proposition_5_4.md)
- [Theorem 5.6](1980_Theorem_5_6.md)
- [Exercise 5.7](1980_Exercise_5_7.md)
- [Exercise 5.8](1980_Exercise_5_8.md)
- [Exercise 5.9](1980_Exercise_5_9.md)
- [Exercise 5.10](1980_Exercise_5_10.md)
- [Exercise 5.11](1980_Exercise_5_11.md)
- [Exercise 5.12](1980_Exercise_5_12.md)
- [Exercise 5.13](1980_Exercise_5_13.md)
- [Exercise 5.14](1980_Exercise_5_14.md)
- [Exercise 5.15](1980_Exercise_5_15.md)
- [Exercise 5.16](1980_Exercise_5_16.md)

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/PNN_orderIso_prod.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/PNN_orderIso_prod.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/PN_orderIso_PNN.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/PN_orderIso_PNN.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/PN_orderIso_prod.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/PN_orderIso_prod.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/P₀.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/P₀.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/P₀_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/P₀_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/P₁.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/P₁.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/P₁_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/P₁_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/compC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/compC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/compC_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/compC_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/compC_eq_comp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/compC_eq_comp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/compMapTbl.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/compMapTbl.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/constC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/constC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/constC_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/constC_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/constC_eq_constMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/constC_eq_constMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/curryC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/curryC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/curryC_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/curryC_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/curryC_toApproxMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/curryC_toApproxMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/curryIso.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/curryIso.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/diagC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/diagC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/diagC_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/diagC_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/evalC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/evalC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/evalC_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/evalC_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/fixC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/fixC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/fixC_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/fixC_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/fixC_fixed.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/fixC_fixed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/funpairC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/funpairC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/funpairC_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/funpairC_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/funpairC_eq_paired.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/funpairC_eq_paired.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/funpairMapTbl.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/funpairMapTbl.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/pairC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/pairC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/pairC_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/pairC_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/swapC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/swapC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Table55/swapC_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Table55/swapC_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/nextCell.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/nextCell.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/num.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/num.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/numEquiv.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/numEquiv.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/numEquiv_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/numEquiv_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/numP.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/numP.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/numP_nextCell.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/numP_nextCell.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/numP_unnum.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/numP_unnum.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/num_injective.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/num_injective.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/num_lt_tri_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/num_lt_tri_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/num_succ_left.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/num_succ_left.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/num_succ_right.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/num_succ_right.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/num_zero_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/num_zero_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/setCongr.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/setCongr.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/tri.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/tri.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/tri_le_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/tri_le_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/tri_mono.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/tri_mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/tri_mul_two.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/tri_mul_two.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/tri_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/tri_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/two_dvd_mul_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/two_dvd_mul_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/unnum.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/unnum.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/unnum_numP.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/unnum_numP.lean)
