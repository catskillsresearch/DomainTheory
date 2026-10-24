# Theorem 5.1

## Human-English

**THEOREM 5.1.** Every typed $\lambda$-term $\tau$ defines an approximable function of its free variables.

*Proof:* We argue by an induction on the complexity of $\tau$; there will only be a few cases to consider since the "syntax" of $\lambda$-terms is limited — even though terms can be of any length.

If $\tau$ is a variable or a constant there is nothing to prove. We already know that

$$x \mapsto x \qquad \text{and} \qquad x \mapsto k$$

are approximable functions.

Suppose $\tau$ has the form

$$\langle \sigma_0, \dots, \sigma_{n-1} \rangle .$$

Then the $\sigma_i$ are less complex terms, and so we can assume — as our induction hypothesis — that they define approximable functions of the free variables. Having said this, we just apply the already

<!-- page 78 -->

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

<!-- page 79 -->

$$\lambda x . \tau = \lambda y . \tau [y / x]$$

is true, provided $y$ does not occur free in the term $\tau$, since the systematic generation of the function defined by $\lambda x . \tau$ does not depend on what the variable $x$ *looks like* but only on its *position* in the term $\tau$. Some other obviously desirable rules for generating true equations are stated in the exercises. But one rule is so basic that we state it here in full generality.

## AI: Human-English to AI-Lean

**[Theorem_5_1.lean](Theorem_5_1.lean)**

@import "Theorem_5_1.lean"
