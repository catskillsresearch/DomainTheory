# Theorem 4.6

**THEOREM 4.6 (The limit theorem).** *Suppose $F$ is a continuous function that maps retracts to retracts and let $c = \mathbf{Y}(F)$. Then $c$ is also a retract. If in addition $F$ maps strict retracts to strict retracts and is monotone in the sense that $a \sqsubseteq b$ implies $F(a) \sqsubseteq F(b)$ for all (strict) retracts $a$ and $b$, then the range of $c$ is homeomorphic to the inverse limit of the ranges of the strict retracts $F^n(\bot)$ for $n \in \omega$.*

This can be applied to the case of (4.38) where $F = \lambda z.\, \mathbf{nil} \oplus (z \otimes z)$. Thus we can analyze **tree** as an inverse limit. This approach has the great advantage over the earlier method of the author where limits were required in showing that **tree** exists. Here we use **Y** to give existence at once, and then apply Theorems 4.3–4.5 to figure out the nature of the retract.

In Theorem 4.6, the fact that $c$ is a retract can be reasoned as follows: $\bot$ is a retract. Thus each $F^n(\bot)$ is a retract. We compute:

$$c \circ c = \bigcup \{F^n(\bot) \mid n \in \omega\} \circ \bigcup \{F^n(\bot) \mid n \in \omega\}$$

$$= \bigcup \{F^n(\bot) \circ F^n(\bot) \mid n \in \omega\} \quad \text{(Note: same $n$.)}$$

$$= \bigcup \{F^n(\bot) \mid n \in \omega\} = c.$$

In case $F$ is monotone and preserves strictness, then we can argue that each $F^n(\bot) \sqsubseteq c$. The retracts $F^n(\bot)$ are the *projections* of $c$ onto the terms of the limit. Of course $F^n(\bot) \sqsubseteq F^m(\bot)$ if $n \le m$. The $u : c$ can be put into a one-to-one correspondence (homeomorphism, lattice isomorphism) with the infinite sequences $\langle v_0, v_1, \ldots, v_n, \ldots \rangle$, where $v_n : F^n(\bot)$ and $v_n = F^n(\bot)(v_{n+1})$. Indeed $v_n = F^n(\bot)(u)$ and $u = \bigcup \{v_n \mid n \in \omega\}$. This is exactly the inverse limit construction.

Retreating from generalities back to the example of **tree**, we can grant that it exists and is provably a retract. Two things in its range are $\bot$ and $\top$ by Theorem 4.5(ii), but they are not so interesting. Now $\bot : \mathbf{nil}$, so by Theorem 4.5(ii) we have $\langle 0 \rangle = \langle 0, \bot \rangle : \mathbf{tree}$. Let us think of this as *the* atom. What else can we have? If $x, y : \mathbf{tree}$, then $\langle x, y \rangle : \mathbf{tree} \otimes \mathbf{tree}$ and so $\langle 1, \langle x, y \rangle \rangle : \mathbf{tree}$. Thus (the range of) **tree** contains an atom and is closed under a binary operation. Note that the atomic and nonatomic trees are distinguished by **which** and that suitable constructor and destructor functions are definable on **tree**. But the space also contains infinite trees since we can solve for the least fixed point of:

$$t = \langle 1, \langle \langle 0 \rangle, t \rangle \rangle$$

and $t : \mathbf{tree}$. (Why?) And there are many other examples of infinite elements in **tree**.

A point to stress in this construction is that **tree** being LAMBDA-definable is *computable*, and there are many computable functions definable on or to (the range of) **tree**. All the "structural" functions, for example, are computable. These are functions which in other languages would be called **isatom** or **construct** or **node**, and they are all easily LAMBDA-definable. Just as with $\oplus$, $\otimes$, $\circ\to$, they are not explicit in the *notation*, but they are definable nevertheless. In the case of **node**, we could use finite sequences of Boolean values to pick out or name nodes. Thus solve for $\mathbf{name} = \mathbf{nil} \oplus \mathbf{bool} \otimes \mathbf{name}$, and then give a recursive definition of:

$$\mathbf{node} : \mathbf{name} \circ\to (\mathbf{tree} \circ\to \mathbf{tree}).$$

Any combination of retract preserving functors can be used in this game. For example:

$$(4.39) \quad \mathbf{lamb} = \mathbf{int} \oplus (\mathbf{lamb} \circ\to \mathbf{lamb}).$$

This looks innocent, but the range of **lamb** would give a quite different and not unattractive model for the $\lambda$-calculus (plus arithmetic). What we do to investigate this model is to modify LAMBDA slightly by replacing the ternary conditional $z \supset x, y$ by a quaternary one $w \supset x, y, z$; otherwise the syntax of the language remains the same. The semantics, however, is a little more complex.

Let us use $\tau$, $\sigma$, $\rho$, $\theta$ as syntactical variables for expressions in the modified language. The semantics is provided by a function $\mathcal{H}$ that maps the expressions of the language to their values in (the range of) **lamb**. To be completely rigorous we also have to confront the question of free and bound variables. For simplicity let us index the variables of the language by integers, and let us take the variables to be $v_0, v_1, v_2, \dots, v_n, \dots$. We cannot simply evaluate out an expression $\tau$ to its value $\mathcal{H}\llbracket \tau \rrbracket$ until we know the values of the free variables in $\tau$. The values of these variables will be given by an "environment" $t$ which can be construed as a *sequence* of values in **lamb**. We can restrict these environments to the retract:

$$(4.40) \quad \mathbf{env} = \lambda t.\, \mathbf{lamb} \circ \mathbf{seq}(t).$$

When $t : \mathbf{env}$, then $t_n : \mathbf{lamb}$ is the value that the environment gives to the variable $v_n$. We also need to employ a transformation on environments as follows:

$$(4.41) \quad t[x/n] = \lambda m \in \omega.\, \mathbf{eq}(n)(m) \supset x,\, t_m.$$

Here **eq** is the primitive recursive function that is $0$, if $n, m$ are equal, and is $1$, otherwise, for $n, m \in \omega$. The effect of $t[x/n]$ is to replace the $n$th term of the sequence $t$ by the value of $x$, otherwise to leave the rest of the sequence unchanged. To correspond with our use of very simple variables we have selected a simple notion of environment: in the semantics of more general languages it is customary to regard an environment as a function from the set of variables into the domain of denotable values.

The correct way to evaluate a term $\tau$ given an environment $t$ is to find $\mathcal{H}\llbracket \tau \rrbracket(t)$. We use the brackets $\llbracket$ and $\rrbracket$ here simply as an aid to the eye in keeping the syntactical part separated from the rest. The environment enters as a function-argument in the usual way; thus we shall have:

$$(4.42) \quad \mathcal{H}\llbracket \tau \rrbracket : \mathbf{env} \to \mathbf{lamb}.$$

$$(4.43) \quad \begin{aligned}
\mathcal{H}\llbracket v_n \rrbracket(t) &= t_n \\
\mathcal{H}\llbracket 0 \rrbracket(t) &= \mathbf{inleft}(0) \\
\mathcal{H}\llbracket \tau + 1 \rrbracket(t) &= \mathbf{which}(\mathcal{H}\llbracket \tau \rrbracket(t) \supset \mathbf{inleft}(\mathbf{out}(\mathcal{H}\llbracket \tau \rrbracket(t)) + 1),\, \bot) \\
\mathcal{H}\llbracket \tau - 1 \rrbracket(t) &= \mathbf{which}(\mathcal{H}\llbracket \tau \rrbracket(t) \supset \mathbf{inleft}(\mathbf{out}(\mathcal{H}\llbracket \tau \rrbracket(t)) - 1),\, \bot) \\
\mathcal{H}\llbracket \theta \supset \tau, \sigma, \rho \rrbracket(t) &= \mathbf{lamb}(\mathbf{which}(\mathcal{H}\llbracket \theta \rrbracket(t) \supset (\mathbf{out}(\mathcal{H}\llbracket \theta \rrbracket(t)) \supset \mathcal{H}\llbracket \tau \rrbracket(t),\, \mathcal{H}\llbracket \sigma \rrbracket(t)),\, \mathcal{H}\llbracket \rho \rrbracket(t))) \\
\mathcal{H}\llbracket \tau(\sigma) \rrbracket(t) &= \mathbf{which}(\mathcal{H}\llbracket \tau \rrbracket(t) \supset \bot,\, \mathbf{out}(\mathcal{H}\llbracket \tau \rrbracket(t))(\mathcal{H}\llbracket \sigma \rrbracket(t))) \\
\mathcal{H}\llbracket \lambda v_n.\,\tau \rrbracket(t) &= \mathbf{inright}(\lambda x : \mathbf{lamb}.\, \mathcal{H}\llbracket \tau \rrbracket(t[x/n])).
\end{aligned}$$

A good question is: why does $\mathcal{H}$ exist? The answer is: because of the fixed-point theorem.

If we rewrite the semantic equations $\mathcal{H}\llbracket \tau \rrbracket(t) = (\dots)$ in (43) by the equation $\mathcal{H}\llbracket \tau \rrbracket = \lambda t : \mathbf{env}\, (\dots)$, then $\mathcal{H}$ is seen to be a function from expressions to values in **lamb**. As the range of **lamb** is contained in $\mathbf{P}\omega$, we can say more broadly that $\mathcal{H} \in \mathbf{P}\omega^{\mathbf{Exp}}$, where **Exp** is the syntactical set of expressions and the exponential notation designates the set of *all* functions from **Exp** into $\mathbf{P}\omega$. This function set is a complete lattice because $\mathbf{P}\omega$ is. Therefore if we read (4.43) as a definition by cases on **Exp**, then we can find $\mathcal{H}$ as a suitable fixed point in the complete lattice $\mathbf{P}\omega^{\mathbf{Exp}}$. Indeed it is the fixed point of a continuous operator.

Actually we can regard **Exp** as being a subset of $\mathbf{P}\omega$ to avoid dragging in other lattices. What we need is another recursive definition of a data type:

$$(4.44) \quad \mathbf{exp} = \mathbf{int} \oplus \mathbf{nil} \oplus \mathbf{exp} \oplus \mathbf{exp} \oplus (\mathbf{exp} \otimes \mathbf{exp} \otimes \mathbf{exp} \otimes \mathbf{exp})$$
$$\qquad \oplus (\mathbf{exp} \otimes \mathbf{exp}) \oplus (\mathbf{int} \otimes \mathbf{exp}).$$

Note that there are as many summands in (4.44) as there are clauses in (4.43). We can think of **exp** as giving the “abstract” syntax of the language. We use the integers to index the variables and the **nil** element to stand for the individual constant. Read (4.44) as saying that every expression is *either* a variable *or* a constant *or* the successor of an expression *or* the predecessor of an expression *or* the conditional formed from a tuple of expressions *or* the abstraction formed from a pair of a variable and an expression. We do not need in (4.44) to introduce special “symbols” for the successor, application, etc., because the separation by cases given by the $\oplus$ operation is sufficient to make the distinctions. (That is why the syntax is “abstract”.) The point is that for recursive definitions it does not matter how we make the distinctions as long as they can be made. From this new point of view, we could rewrite (4.43) so as to show:

$$(4.45) \quad \mathcal{H} : \mathbf{exp} \to (\mathbf{env} \to \mathbf{lamb}),$$

which is clearly more satisfactory—especially as it is now clear that $\mathcal{H}$ is *computable*. And this is a method that can be generalized to many other languages. The method also shows why it is useful to allow *function spaces* as particular data types.

Another example of this method can be illustrated, if the reader will recall the Gödel numbering of § 3. It will be seen that there are similarities with the **tree** construction: instead of $0$ and $\mathbf{apply}(n)(m)$, **tree** uses $\langle 0 \rangle$ and $\langle 1, \langle x, y \rangle \rangle$. Note, however, that Gödel numbers are *finite* while **tree** has *infinite* objects. But the infinite objects are always *limits* of finite objects, so there *are* connections. (We discuss this again in § 6.) In particular, recursive definitions on Gödel numbers, like that of **val**, have analogues on **tree**. Here is the companion of (3.7):

$$(4.46) \quad \mathbf{vaal} = \lambda x : \mathbf{tree}.\, \mathbf{which}(x) \supset \mathbf{G},\, \mathbf{vaal}(\mathbf{fst}(\mathbf{out}(x)))(\mathbf{vaal}(\mathbf{snd}(\mathbf{out}(x)))).$$

We have $\mathbf{vaal} : \mathbf{tree} \to \mathbf{id}$, where of course (4.46) is taken as defining **vaal** as the least fixed point. This is an example of a computable function between effectively given retracts. The LAMBDA-definable elements of $\mathbf{P}\omega$ are the computable elements in the range of **vaal**.

We have discussed the category of retracts and continuous maps, but if they are all LAMBDA-definable, then they fall within the countable model **RE**. Thus there is *another* category of effectively given retracts and effectively given continuous maps. (Examples: **tree**, **id**, **vaal**, and all those retracts and maps generated by $\oplus$, $\otimes$, and $\circ\to$.) This category seems to deserve the status of a generalized recursion theory; though this is not to say that as yet very much is known about it. In fact, the proper formulation may require an enriched category rather than a restricted one. Thus instead of confining attention to the computable retracts and computable maps, it might be better to use the full category with all maps and to single out the computable ones (also maybe the finite ones) by special predicates. In effect we have avoided any methodological decisions by working in the universal space $\mathbf{P}\omega$ and by *defining* a notion when required—if possible with the aid of LAMBDA. This makes it possible to give all the necessary definitions and to prove the theorems without at first having to worry about axiomatic problems.

**Lean 4**

- [DataTypesAsLattices/Retracts/theorem_4_6.lean](theorem_4_6.lean)
- [DataTypesAsLattices/Retracts/theorem_4_6_inverseLimit.lean](theorem_4_6_inverseLimit.lean)
- [DataTypesAsLattices/Retracts/theorem_4_6_limit.lean](theorem_4_6_limit.lean)
