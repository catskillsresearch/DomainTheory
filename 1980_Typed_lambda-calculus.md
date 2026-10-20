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

**THEOREM 5.1.** Every typed $\lambda$-term $\tau$ defines an approximable function of its free variables.

*Proof:* We argue by an induction on the complexity of $\tau$; there will only be a few cases to consider since the "syntax" of $\lambda$-terms is limited — even though terms can be of any length.

If $\tau$ is a variable or a constant there is nothing to prove. We already know that

$$x \mapsto x \qquad \text{and} \qquad x \mapsto k$$

are approximable functions.

Suppose $\tau$ has the form

$$\langle \sigma_0, \dots, \sigma_{n-1} \rangle .$$

Then the $\sigma_i$ are less complex terms, and so we can assume — as our induction hypothesis — that they define approximable functions of the free variables. Having said this, we just apply the already
proved 3.4 to conclude (after a suitable generalization to the multivariate case) that $\tau$, which takes on tuples as values, also defines an approximable function.

Next, suppose $\tau$ has the form

$$\sigma_0(\sigma_1),$$

where we are sure that the types of all the terms match properly. Again we can assume the $\sigma_i$ to be well behaved. But the values we seek can also be written as

$$\mathrm{eval}(\sigma_0, \sigma_1).$$

Since eval is approximable by 3.11, we just have to invoke an instance of 3.7 to gain the desired conclusion.

Finally, suppose that $\tau$ has the form

$$\lambda x . \sigma.$$

By a judicious choice of the order of the variables in $\sigma$ (including $x$), we can assume that $\sigma$ defines an approximable function

$$g : D_0 \times \cdots \times D_{n-1} \times D_n \to D'$$

where $D'$ is the type of $\sigma$, $D_n$ is the type of $x$, and $D_0, \dots, D_{n-1}$ are the types of the remaining free variables of $\sigma$. We apply 3.12 and obtain an approximable function

$$\mathrm{curry}(g) : D_0 \times \cdots \times D_{n-1} \to (D_n \to D').$$

But, this is just exactly the function defined by $\tau$.

We leave as an exercise the more general case of a term $\tau$ of the form

$$\lambda x_0, \dots, x_{k-1} . \sigma,$$

which has a string of bound variables. $\square$

We can now say more precisely what it means to call $\sigma = \tau$ a "true equation". This means that, if we employ the method of the proof of 5.1, the two terms define the *same function* of the free variables. For example,
$$\lambda x . \tau = \lambda y . \tau [y / x]$$

is true, provided $y$ does not occur free in the term $\tau$, since the systematic generation of the function defined by $\lambda x . \tau$ does not depend on what the variable $x$ *looks like* but only on its *position* in the term $\tau$. Some other obviously desirable rules for generating true equations are stated in the exercises. But one rule is so basic that we state it here in full generality.

**THEOREM 5.2.** For suitably typed $\lambda$-terms the following equation is true:

$$(\lambda x_0, \ldots, x_{n-1} \cdot \tau)(\sigma_0, \ldots, \sigma_{n-1}) = \tau [\sigma_0 / x_0, \ldots, \sigma_{n-1} / x_{n-1}].$$

*Proof:* It will be sufficient to carry out the proof for $n = 1$. The proof proceeds by induction on the complexity of the term $\tau$.

In case $\tau$ is a *constant* $k$, the result reads

$$(\lambda x . k)(\sigma) = k,$$

and this is a true equation.

In case $\tau$ is a *variable* (in particular, the variable $x$), the result reads

$$(\lambda x . x)(\sigma) = \sigma,$$

and again this is a true equation.

In case $\tau$ is a *tuple* (say, $\langle \tau_0, \tau_1 \rangle$) the result reads

$$(\lambda x . \langle \tau_0, \tau_1 \rangle)(\sigma) = \langle \tau_0 [\sigma / x], \tau_1 [\sigma / x] \rangle .$$

This is true, because the left-hand side can be transformed by the true equation

$$(\lambda x . \langle \tau_0, \tau_1 \rangle)(\sigma) = \langle (\lambda x . \tau_0)(\sigma), (\lambda x . \tau_1)(\sigma) \rangle;$$

and then we apply the inductive assumption for $\tau_0$ and for $\tau_1$.

In case $\tau$ is an *application*, we want (supposing the term is $\tau_0 (\tau_1)$),

$$(\lambda x . \tau_0 (\tau_1))(\sigma) = \tau_0 [\sigma / x] (\tau_1 [\sigma / x]) .$$

We can proceed as in the last case, noting that the left-hand side equals
$$
\mathrm{eval}\ ((\lambda x . \langle \tau_0 , \tau_1 \rangle)\ (\sigma))\ .
$$

In case $\tau$ is an *abstract* (say, $\lambda y . \tau_0$), we want

$$
(\lambda x . \lambda y . \tau_0)\ (\sigma) = \lambda y . \tau_0 [\sigma / x]
$$

*PROVIDED* the variable $y$ is not free in $\sigma$. For this we require the true equation

$$
(\lambda x . \lambda y . \tau)\ (\sigma) = \lambda y . (\lambda x . \tau)\ (\sigma)\ .
$$

We argue for this by letting $g$ be the function of $n + 2$ free variables defined by $\tau$. Then, by 5.1, the $\lambda$-term $\lambda x . \lambda y . \tau$ defines the function $\mathrm{curry}\ (\mathrm{curry}\ (g))$ of $n$ arguments. We can call this function $h$ for the moment. We can write

$$
h(v)\ (\sigma)\ (y) = g(v, \sigma, y)\ ,
$$

where $v$ is a list of arguments. But, with an appropriate combinator $\mathrm{inv}$, which applied to $g$ inverts the order of the last two arguments, we can write

$$
h(v)\ (\sigma)\ (y) = \mathrm{curry}\ (\mathrm{inv}\ (g))\ (v, y)\ (\sigma)\ .
$$

But, $\mathrm{curry}\ (\mathrm{inv}\ (g))$ is just the function defined by $(\lambda x . \tau)$. So what we have proved as true is

$$
(\lambda x . \lambda y . \tau)\ (\sigma)\ (y) = (\lambda x . \tau)\ (\sigma)\ .
$$

But if $y$ is not free in $\alpha$ and

$$
\alpha(y) = \beta
$$

is true, then so is

$$
\alpha = \lambda y . \beta\ .
$$

This completes the proof. $\square$

We note that if $\tau'$ is the term $\lambda x, y . \tau$, then $\tau'(x, y)$ means the same as $\tau$. This gives a convenient way of indicating free variables: we just write $\sigma(x, y)$ — where $x, y$ are not free in $\sigma$ — and this will have the same values as any term $\tau$ which does involve the extra free variables $x$ and $y$. We use this notational device in the next theorem.
**PROPOSITION 5.3.** The least fixed point of $\lambda x, y.\ \langle \tau(x, y), \sigma(x, y) \rangle$ is the pair with coordinates

$! x.\ \tau(x,\ ! y.\ \sigma(x, y))$ and

$! y.\ \sigma(! x.\ \tau(x, y), y)$.

**Proof:** (We are assuming that $x$ and $y$ are not free in $\tau$ and $\sigma$.) The purpose of the fixed-point search is to find the least solution of the pair of equations $x = \tau(x, y)$ and $y = \sigma(x, y)$. In other words, we are generalizing the fixed-point equation from one to two variables—and, of course, we could go much further to any number of variables. To this end, let

$y_* = ! y.\ \sigma(! x.\ \tau(x, y), y)$, and

$x_* = ! x.\ \tau(x, y_*)$.

Then

$x_* = \tau(x_*, y_*)$,

and

$y_* = \sigma(! x.\ \tau(x, y_*), y_*)$

$= \sigma(x_*, y_*)$.

This proves that $\langle x_*, y_* \rangle$ is one fixed-point pair.

Suppose, then, that $\langle x_0, y_0 \rangle$ is the least solution. (Why does a least solution have to exist? Hint: Consider a suitable mapping of type $D_0 \times D_1 \to D_0 \times D_1$, where $D_0$ is the type of $x$ and $D_1$ the type of $y$.) Then we know $x_0 = \tau(x_0, y_0)$ and $y_0 = \sigma(x_0, y_0)$, and also $x_0 \sqsubseteq x_*$ and $y_0 \sqsubseteq y_*$. But from

$\tau(x_0, y_0) \sqsubseteq x_0$,

it follows that

$! x.\ \tau(x, y_0) \sqsubseteq x_0$.
Consequently,

$$\sigma(! x . \tau(x, y_0), y_0) \sqsubseteq \sigma(x_0, y_0) \sqsubseteq y_0.$$

By the fixed-point definition of $y_*$, we have $y_* \sqsubseteq y_0$, so $y_* = y_0$; whence,

$$x_* = ! x . \tau(x, y_*) = ! x . \tau(x, y_0) \sqsubseteq x_0.$$

So also $x_* = x_0$. $\square$ We have the right formula for $y_0$, and a similar argument gives $x_0$.

The purpose of giving the above proof was to illustrate the use of the least fixed-point operator in proofs. We have such true principles as:

$$! x . \tau(x) = \tau(! x . \tau(x));$$

and

$$\tau(y) \sqsubseteq y \text{ implies } ! x . \tau(x) \sqsubseteq y,$$

provided, of course, that $x$ is not free in $\tau$. These, together with the monotonicity of all the functions, were just the methods used in the above proof. Here is another example.

**PROPOSITION 5.4.** Let $x$, $y$, and $\tau(x, y)$ be of the same type $D$ and let $g$ be of type $(D \to D)$, then the equation

$$\lambda x . ! y . \tau(x, y) = ! g . \lambda x . \tau(x, g(x))$$

is true.

*Proof :* Let $f$ be the function on the left-hand side. We can write

$$f(x) = ! y . \tau(x, y) = \tau(x, f(x)).$$

Therefore

$$f = \lambda x . \tau(x, f(x)),$$

and it follows that

$$g_0 = ! g . \lambda x . \tau(x, g(x)) \sqsubseteq f.$$

Then we have at once, by definition of $g_0$,

$$g_0(x) = \tau(x, g_0(x)),$$

for any given $x$. But by definition of $f$ we find

$$f(x) = ! y . \tau(x, y) \sqsubseteq g_0(x).$$
As this holds for all $x$, then $f \sqsubseteq g_0$ follows. So the equation is true. $\square$

The last proof is instructive as it uses equations and inclusions between functions. In particular we have just made use of the principle:

> if $\tau \sqsubseteq \sigma$ holds for all values of $x$,  
> then $\lambda x . \tau \sqsubseteq \lambda x . \sigma$ holds.

This is another form of Theorem 3.13(i).

**TABLE 5.5.** In the displayed table we give a summary of uses of the $\lambda$-notation to define various combinators. We have mentioned some of these equations before, and there are some combinators here we have not mentioned before — their meanings, however, should be clear.

$$
\begin{aligned}
P_0 &= \lambda x, y . x \\
P_1 &= \lambda x, y . y \\
\mathrm{pair} &= \lambda x \lambda y . \langle x, y \rangle \\
\mathrm{n\text{-}tuple} &= \lambda x_0 \lambda x_1 \ldots \lambda x_{n-1} . \langle x_0, x_1, \ldots, x_{n-1} \rangle \\
\mathrm{diag} &= \lambda x . \langle x, x \rangle \\
\mathrm{funpair} &= \lambda f \lambda g \lambda x . \langle f(x), g(x) \rangle \\
\mathrm{proj}_i^n &= \lambda x_0, x_1, \ldots, x_{n-1} . x_i \\
\mathrm{inv}_{i,j}^n &= \lambda x_0, \ldots, x_i, \ldots, x_j, \ldots, x_{n-1} . \langle x_0, \ldots, x_j, \ldots, x_i, \ldots, x_{n-1} \rangle
\end{aligned}
$$

$$
\begin{aligned}
\mathrm{eval} &= \lambda f, x . f(x) \\
\mathrm{curry} &= \lambda g \lambda x \lambda y . g(x, y) \\
\mathrm{comp} &= \lambda g, f \lambda x . g(f(x)) \\
\mathrm{const} &= \lambda k \lambda x . k \\
\mathrm{fix} &= \lambda f ! x . f(x)
\end{aligned}
$$

**A TABLE OF COMBINATORS**
It is important to note that since we have not typed the variables, these equations are ambiguous: they only become precise when the types are specified. It follows, therefore, that what we find in the table are *schemes* for combinators; there are actually infinitely many distinct combinators corresponding to any one equation depending on how the variables have types chosen for them. Clearly it is better to imagine this variety of combinators than it is to try to notate them with type superscripts.

One interest of combinators is that it is often possible to write expressions without variables — if enough combinators are used. This is sometimes useful, but it can become clumsy. On the other hand, if the same combination occurs over and over, it is sometimes useful to give it a name. This is what we do with, say, *composition* where

$$
\mathrm{comp}\ (g, f) = g \circ f.
$$

On the one side we have the prefix notation, and on the other, the more common infix notation. With either notation the variable seen in $\lambda x.\ g(f(x))$ has been got rid of. The choice between equivalent notations ought to be based on a desire for readability. $\square$

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

What is *not* said in 5.6 is that every $\lambda$-term defines a partial recursive function. This is true (with suitable control over the constants and types in the expression), but the proof requires a full analysis of computability properties of domain constructions. This is the topic of Lecture VII.

It should be remarked that the types of variables needed for the proof of 5.6 never get very high. In fact, types like $N$, $N^k$, and $(N^k \to N)$ were the only ones needed (with perhaps $T$ thrown in also).

Recursion on $N$ was the topic of 5.6; further examples of recursion on other domains are included in the exercises.

## EXERCISES

**EXERCISE 5.7.** Find definitions of

$$\lambda x, y.\, \tau \quad \text{and} \quad \sigma(x, y)$$

which use only $\lambda v$ with one variable and applications only to one argument at a time. Note that use must be made of the combinators $p_0$, $p_1$, pair. Generalize the result to functions of many variables.
**EXERCISE 5.8.** (For combinator nuts.) Table 5.5 was meant to show how combinators could be defined in terms of $\lambda$-expressions. Can the tables be turned to show that with enough combinators available, every $\lambda$-expression can be defined by combining combinators, using $\sigma(\tau)$ as the *only* mode of combination?

**EXERCISE 5.9.** Suppose that $f, g : \mathcal{D} \to \mathcal{D}$ are approximable and $f \circ g = g \circ f$. Show that $f$ and $g$ have a *least common fixed point* $x = f(x) = g(x)$. (Hint: Refer back to Exercise 4.20.) If in addition $f(\bot) = g(\bot)$, show that $\mathrm{fix}(f) = \mathrm{fix}(g)$. In particular, will $\mathrm{fix}(f) = \mathrm{fix}(f^2)$? What if we only assume $f \circ g = g^2 \circ f$?

**EXERCISE 5.10.** Suppose $\mathcal{D}_0$ and $\mathcal{D}_1$ are neighbourhood systems over disjoint sets $\Delta_0$ and $\Delta_1$. Define the *smash product* $\mathcal{D}_0 \otimes \mathcal{D}_1$ with neighbourhoods

$$
\{\Delta_0 \cup \Delta_1\} \cup \{X \cup Y \mid X \in \mathcal{D}_0 \setminus \{\Delta_0\} \text{ and } Y \in \mathcal{D}_1 \setminus \{\Delta_1\}\}.
$$

Show that this *is* a neighbourhood system. Define $(\mathcal{D}_0 \to_\bot \mathcal{D}_1)$ so that $|\mathcal{D}_0 \to_\bot \mathcal{D}_1|$ consists exactly of the *strict functions*. By introducing appropriate combinators, show that

$$
(\mathcal{D}_0 \to_\bot (\mathcal{D}_1 \to_\bot \mathcal{D}_2)) \quad \text{and} \quad ((\mathcal{D}_0 \otimes \mathcal{D}_1) \to_\bot \mathcal{D}_2)
$$

are isomorphic.

**EXERCISE 5.11.** For any domain $\mathcal{D}$ we may regard $\mathcal{D}^\infty$ as consisting of (bottomless) *stacks* of elements of $\mathcal{D}$. With this image in mind, define appropriate combinators with the obvious meanings:

$$
\mathrm{head} : \mathcal{D}^\infty \to \mathcal{D};\quad
\mathrm{tail} : \mathcal{D}^\infty \to \mathcal{D}^\infty;\quad
\mathrm{push} : \mathcal{D} \times \mathcal{D}^\infty \to \mathcal{D}^\infty.
$$

Using the fixed-point theorem argue that there is a combinator

$$
\mathrm{diag} : \mathcal{D} \to \mathcal{D}^\infty
$$

where for all $x \in |\mathcal{D}|$ we have

$$
\mathrm{diag}(x) = \langle x \rangle_{n=0}^\infty.
$$
(Hint: Try a recursive definition, say

$$
\mathrm{diag}(x) = \mathrm{push}(x, \mathrm{diag}(x)),
$$

but be sure to prove *all* terms of $\mathrm{diag}(x)$ equal $x$.) Also introduce by an appropriate recursion a combinator

$$
\mathrm{map} : (D \to D)^\infty \times D \to D^\infty
$$

where for elements of the suitable types:

$$
\mathrm{map}(\langle f_n \rangle_{n=0}^\infty, x) = \langle f_n(x) \rangle_{n=0}^\infty.
$$

**EXERCISE 5.12.** On any domain $D$ introduce (as a least fixed point) a combinator

$$
\mathrm{while} : (D \to T) \times (D \to D) \to (D \to D)
$$

by the recursion

$$
\mathrm{while}(p, f)(x) = \mathrm{cond}(p(x), \mathrm{while}(p, f)(f(x)), x).
$$

Prove that

$$
\mathrm{while}(p, \mathrm{while}(p, f)) = \mathrm{while}(p, f).
$$

Show how $\mathrm{while}$ could have been used to obtain the least number operator mentioned in the proof of 5.6. Generalize the idea to define a combinator

$$
\mathrm{find} : D^\infty \times (D \to T) \to D
$$

with the meaning "find the first term of the sequence (if any) which satisfies the given precicate."

**EXERCISE 5.13.** Prove the existence of a one-one function $\mathrm{num} : \mathbf{N} \times \mathbf{N} \to \mathbf{N}$ such that

$$
\mathrm{num}(0, 0) = 0;
$$

$$
\mathrm{num}(n, m+1) = \mathrm{num}(n+1, m) + 1;
$$

$$
\mathrm{num}(n+1, 0) = \mathrm{num}(0, n) + 1.
$$

Draw a picture (i.e. an infinite matrix) for the function and find a closed form for its values, if possible. Use the function to prove the isomorphism of the domains

$$
P\mathbf{N},\ P(\mathbf{N} \times \mathbf{N}),\ P\mathbf{N} \times P\mathbf{N}.
$$
**EXERCISE 5.14.** Show that there are approximable mappings

$$
\mathrm{graph} : (P\mathbf{N} \to P\mathbf{N}) \to P\mathbf{N} \quad \text{and} \quad \mathrm{fun} : P\mathbf{N} \to (P\mathbf{N} \to P\mathbf{N}),
$$

where we have

$$
\mathrm{fun} \circ \mathrm{graph} = \lambda f.\, f, \quad \text{and} \quad \mathrm{graph} \circ \mathrm{fun} \supseteq \lambda x.\, x.
$$

(Hint: Using the notation

$$
[n_0, n_1, \ldots, n_k] = \mathrm{num}(n_0, [n_1, \ldots, n_k])
$$

two such combinators can be given by formulae

$$
\mathrm{fun}(u)(x) = \{m \mid \exists n_0, \ldots, n_{k-1} \in x.\ [n_0+1, \ldots, n_{k-1}+1, 0, m] \in u\}
$$

$$
\mathrm{graph}(f) = \{[n_0+1, \ldots, n_{k-1}+1, 0, m] \mid m \in f(\{n_0, \ldots, n_{k-1}\})\}
$$

where $k$ is variable — meaning all finite sequences are to be considered.)

**EXERCISE 5.15.** (For algebraists.) We can regard $\langle \{0,1\}^*, \Lambda, \cdot \rangle$ as the free semigroup on two generators $0$ and $1$. The powerset $P\{0,1\}^*$ is taken as a domain as in Exercise 4.17. For "words" $e \in \{0,1\}^*$ define

$$
e^* = \{\Lambda, e, e^2, e^3, \ldots, e^n, \ldots\}.
$$

Show that the least fixed point of

$$
z = \{e\} \cdot z \cup \{e'\}
$$

in $P\{0,1\}^*$ is $z = e^* \cdot \{e'\}$.

Show further (as suggested by David Park) that the least solution of

$$
\begin{aligned}
x &= a \cdot x \cup b \cdot y \cup c, \\
y &= b \cdot x \cup a \cdot y \cup d
\end{aligned}
$$

has

$$
x = (a \cup b \cdot a^* \cdot b)^* \cdot (c \cup b \cdot a^* \cdot d),
$$

where the $\{\cdot\}$ has been dropped off $\{a\}$, $\{b\}$ etc., and where the $^*$-notation has been extended to the whole domain, so that $z^* = \Lambda \cup z^* \cdot z$.

(Hint: Apply 5.3.)
**EXERCISE 5.16.** Return to the discussion of Example 4.4 and the construction of the domain of finite and infinite binary sequences. Give a fixed-point definition of $\mathrm{neg} : C \to C$, where

$$
\mathrm{neg}(0x) = 1\,\mathrm{neg}(x); \qquad \mathrm{neg}(1x) = 0\,\mathrm{neg}(x).
$$

Prove that $\mathrm{neg}(\mathrm{neg}(x)) = x$ for all $x \in |C|$. Also define $\mathrm{merge} : C \times C \to C$, where for $\epsilon, \delta \in \{0, 1\}$ we have:

$$
\mathrm{merge}(\epsilon x, \delta y) = \epsilon\,\delta\,\mathrm{merge}(x, y).
$$

(Note: There may be a little trouble with $\mathrm{merge}(x, y)$ when $x$ is finite and total and $y$ is infinite—you have to decide what you want in e.g. $\mathrm{merge}(\Lambda, y)$.) Prove that

$$
\mathrm{merge}(x, x) = d(x),
$$

in the notation of 4.4. Consider also the infinite non-periodic sequence

$$
t = 0\,\mathrm{merge}(\mathrm{neg}(t), \mathrm{tail}(t)).
$$

Prove that the $n^{\mathrm{th}}$ digit of $t$ is the sum mod 2 of the digits of the number $n$ written in the binary scale (a suggestion of J. Lambek). Show also that $t \neq u\,a\,a\,a\,v$ where $a$ is any finite sequence $\neq \Lambda$, and where $u$ is finite.

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise507.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/app_two_args.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/app_two_args.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/curryu2083_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/curryu2083_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/curry₃.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/curry₃.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/lam_two_vars.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/lam_two_vars.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/surjective_pairing.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/surjective_pairing.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/uncurry_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/uncurry_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/uncurry_lam_two_vars.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise507/uncurry_lam_two_vars.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/CL.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/CL.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Dom.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Dom.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Ielem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Ielem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Ielem_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Ielem_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Kelem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Kelem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Kelem_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Kelem_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Poly.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Poly.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Sbody.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Sbody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Selem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Selem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Selem_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Selem_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Smap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Smap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Smap_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/Smap_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/bracket.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/bracket.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/bracket_spec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/bracket_spec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/toApproxMap_toFilter.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise508/toApproxMap_toFilter.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise509.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/commute_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/commute_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/commuting_least_common_fixed.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/commuting_least_common_fixed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/comp_self_iterElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/comp_self_iterElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/fixElement_eq_of_commuting_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/fixElement_eq_of_commuting_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/fixElement_iterTwice.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/fixElement_iterTwice.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/iterElem_le_fixElement.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/iterElem_le_fixElement.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/iterElem_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/iterElem_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/iterElem_zerou27.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise509/iterElem_zerou27.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/IsStrict.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/IsStrict.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/SmashProper.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/SmashProper.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/StrictMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/StrictMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/eq_bot_of_no_proper.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/eq_bot_of_no_proper.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/exists_proper_of_ne_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/exists_proper_of_ne_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/inter_ne_master_left.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/inter_ne_master_left.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/inter_ne_master_right.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/inter_ne_master_right.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_constBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_constBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_idMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_idMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_iff_apply_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_iff_apply_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_smashSection.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_smashSection.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_smashPair.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_smashPair.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_sstep.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_sstep.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_sstepFun.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_sstepFun.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_sstepFun_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_sstepFun_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_toStrictFilter.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_toStrictFilter.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mono.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/principal_master_eq_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/principal_master_eq_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/rel_sstepFun_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/rel_sstepFun_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/section_uncurry_rel.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/section_uncurry_rel.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashCurryEquiv.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashCurryEquiv.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashCurryMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashCurryMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashCurry_uncurry.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashCurry_uncurry.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_bot_left.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_bot_left.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_bot_right.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_bot_right.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_eq_bot_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_eq_bot_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_mono.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_principal_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_principal_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashSection.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashSection.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashSection_mono.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashSection_mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashSection_rel.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashSection_rel.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashUncurryMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashUncurryMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashUncurry_curry.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashUncurry_curry.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_master.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_master.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_prodNbhd_form.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_prodNbhd_form.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_proper.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_proper.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_append.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_append.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_singleton.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_singleton.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_up_closed.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_up_closed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_cod_master.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_cod_master.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_inter_right.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_inter_right.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_master_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_master_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_mem_of_mem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_mem_of_mem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_subset.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_subset.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFunEquiv.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFunEquiv.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_master.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_master.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_mem_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_mem_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_mem_inter.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_mem_inter.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_mem_up_closed.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_mem_up_closed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/toStrictFilter.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/toStrictFilter.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/toStrictMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/toStrictMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/toStrictMap_rel.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/toStrictMap_rel.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/Arg.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/Arg.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_diag.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_map.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_map.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_tail.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/component_tail.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/diag.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/diag_rec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/diag_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/fold.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/fold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/fold_unfold.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/fold_unfold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head_push.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/head_push.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/iterProdIso_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/iterProdIso_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapBody.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapBody.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapBody_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapBody_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapOp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/mapOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/map_rec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/map_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/push.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/push.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/push_head_tail.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/push_head_tail.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail_push.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/tail_push.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/unfold.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/unfold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/unfold_fold.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise511/unfold_fold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Wop.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Wop.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Wop_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/Wop_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/bodyMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/bodyMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/bodyMap_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/bodyMap_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileFix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileFix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_bot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_false.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_false.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_least.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_least.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_rec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_rec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_true.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise512/whileMap_true.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise513.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise513.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_Graph.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_Graph.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_isApprox.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_isApprox.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_mono.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Graph.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Graph.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/IsApprox.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/IsApprox.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/entries.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/entries.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/id_le_Graph_Fun.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/id_le_Graph_Fun.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/mem_entries.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/mem_entries.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/num_succ_left_gt.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/num_succ_left_gt.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_injective.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_injective.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_surjective.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_surjective.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/G.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/G.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/arden.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/arden.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_kpow_singleton.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_kpow_singleton.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_star.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_star.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_star_singleton.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_star_singleton.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkA.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkA.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkX.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkX.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkX_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkX_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkY.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkY.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkY_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkY_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/park_least.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/park_least.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/park_solves.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/park_solves.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/part1.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/part1.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/part1_freeMonoid.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/part1_freeMonoid.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/smul_assoc.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/smul_assoc.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/smul_union.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/smul_union.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_mul_isFixed.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_mul_isFixed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_mul_subset_prefixed.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_mul_subset_prefixed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/sunion_mul.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/sunion_mul.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe_cons2.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe_cons2.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe_cons_inv.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/SLe_cons_inv.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap_strElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/dMap_strElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/d_hcone.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/d_hcone.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/d_hsing.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/d_hsing.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_append.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_append.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_prefix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/double_prefix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_flip.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_flip.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_prefix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/flip_prefix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/map_ext_C.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/map_ext_C.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/memC_eq_shape.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/memC_eq_shape.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/memC_shape.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/memC_shape.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem_diag.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem_diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem_mono.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeElem_mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_diag.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_pair.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeMap_pair.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_SLe.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_SLe.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_cons_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_cons_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_cons_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_cons_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_diag.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_diag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/mergeVal_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_comp_negMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_comp_negMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_negMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_negMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_strElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/negMap_strElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_cons_false.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_cons_false.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_cons_true.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_cons_true.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_hcone.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_hcone.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_hsing.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/neg_hsing.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/not_strElem_le_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/not_strElem_le_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/prodMap_ext.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/prodMap_ext.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/prod_principal_pair.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/prod_principal_pair.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_false.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_false.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_le_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_le_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_true.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shapeElem_true.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape_injective.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape_injective.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape_refine.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/shape_refine.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strBot_le_strBot_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strBot_le_strBot_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strBot_le_strElem_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strBot_le_strElem_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strElem_le_strElem_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/strElem_le_strElem_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_consMap_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_consMap_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_consMap_strElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_consMap_strElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_strElem.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailMap_strElem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailSing.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tailSing.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_hcone.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_hcone.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_hsing.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_hsing.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_prefix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516/tail_prefix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/Overlap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/Overlap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/append_three_period.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/append_three_period.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_cube.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_cube.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_overlap.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_overlap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_three_consec.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/no_three_consec.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/odd_of_consec_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/odd_of_consec_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tElt_cube_free.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tElt_cube_free.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tmList_getElemu3f.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tmList_getElemu3f.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_of_eq_two_mul.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_of_eq_two_mul.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_of_eq_two_mul_add_one.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_of_eq_two_mul_add_one.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_two_mul_ne.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516Overlap/tm_two_mul_ne.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/cone_univ_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/cone_univ_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_append.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_append.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_iterate_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_iterate_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_tmList.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/expand_tmList.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_le_fixElement.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_le_fixElement.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_succ_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_succ_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_zerou27.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterElem_zerou27.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterate_expand_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/iterate_expand_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/mergeVal_snd_false.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/mergeVal_snd_false.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/strBot_mem_cone.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/strBot_mem_cone.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/strBot_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/strBot_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_digit.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_digit.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_mem_cone_iff.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_mem_cone_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_unfold.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tElt_unfold.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_le_tElt.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_le_tElt.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_length.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_length.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_prefix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_prefix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmList_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp_strBot.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp_strBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp_strBot_expand.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tmOp_strBot_expand.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_two_mul.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_two_mul.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_two_mul_add_one.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_two_mul_add_one.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/tm_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/weave_head.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise516ThueMorse/weave_head.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/PNN_orderIso_prod.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/PNN_orderIso_prod.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/PN_orderIso_PNN.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/PN_orderIso_PNN.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/PN_orderIso_prod.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/PN_orderIso_prod.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition53.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition53.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/fixElement_paired_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/fixElement_paired_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/outerOp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/outerOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/outerOp_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/outerOp_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/secFixX.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/secFixX.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/secFixX_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/secFixX_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/secFixX_isFixed.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/secFixX_isFixed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/sectionX.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/sectionX.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/sectionX_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition53/sectionX_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition54.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix_eq_fixElement_recOp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix_eq_fixElement_recOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix_isFixed.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix_isFixed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/recOp.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/recOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/recOp_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/recOp_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/sectionu2082_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/sectionu2082_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/section₂.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/section₂.lean)
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
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem51.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem51.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/abs_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/abs_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/app_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/app_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/const_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/const_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/tuple_apply.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/tuple_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/var_fst.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/var_fst.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/var_snd.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem51/var_snd.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem52.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem52.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem52/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem52/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem52/beta.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem52/beta.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem52/beta_abs.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem52/beta_abs.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem52/beta_tuple.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem52/beta_tuple.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Theorem52/subst_value.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Theorem52/subst_value.lean)
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
