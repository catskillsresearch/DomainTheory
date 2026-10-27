# Theorem 5.2

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

<!-- page 80 -->

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

<!-- page 81 -->

**[Theorem_5_2.lean](Theorem_5_2.lean)**

@import "Theorem_5_2.lean"
