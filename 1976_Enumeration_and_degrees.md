# Enumeration and degrees

A great advantage of the combinators from the formal point of view is that (bound) variables are eliminated in favor of “algebraic” combinations. The disadvantage is that the algebra is not all that pretty, as the combinations tend to get rather long and general laws are rather few. Nevertheless as a technical device it is mildly remarkable that we can have a notation for all r.e. sets requiring so few primitives. In the model defined here the reduction to one combinator rests on a lemma about conditionals:

$$(3.1) \quad \mathbf{cond}(x)(y)(\mathbf{cond}(x)(y)) = y.$$

Recall that $\mathbf{cond}$ (or $\supset$) is a test for zero, so that:

$$(3.2) \quad \mathbf{cond}(x)(y)(0) = x.$$

This suggests that we lump all combinators of Theorem 2.4 into this one:

$$(3.3) \quad \mathbf{G} = \mathbf{cond}(\langle \mathbf{suc}, \mathbf{pred}, \mathbf{cond}, \mathbf{K}, \mathbf{S} \rangle)(0).$$

We can then readily prove:

**THEOREM 3.1 (The generator theorem).** *All LAMBDA-definable elements can be obtained from* $\mathbf{G}$ *by iterated application.*

A distributive function $f$ is said to be *total* iff $f(n) \in \omega$ for all $n \in \omega$. As they come from obvious primitive recursive functions, we do not stop to write out LAMBDA-definitions of these three total functions:

$$(3.4) \quad \mathbf{apply} = \lambda n \in \omega.\, \lambda m \in \omega.\, (n, m) + 1$$

$$(3.5) \quad \mathbf{op}((n, m)) = n$$

$$(3.6) \quad \mathbf{arg}((n, m)) = m.$$

The point of these auxiliary combinators concerns our Gödel numbering of the r.e. sets. The number 0 will correspond to the generator $\mathbf{G}$; while $(n, m) + 1$ will correspond to the application of the $n$th set to the $m$th. This is formalized in the combinator $\mathbf{val}$ which is defined as the least fixed point of the equation:

$$(3.7) \quad \mathbf{val} = \lambda k \in \omega.\, k \supset \mathbf{G},\, \mathbf{val}(\mathbf{op}(k - 1))(\mathbf{val}(\mathbf{arg}(k - 1))).$$

This function accomplishes the enumeration as follows:

**THEOREM 3.2 (The enumeration theorem).** *The combinator* $\mathbf{val}$ *enumerates the LAMBDA-definable elements in that* $\mathbf{RE} = \{\mathbf{val}(n) \mid n \in \omega\}$. *Further:*

*(i)* $\mathbf{val}(0) = \mathbf{G}$,

*(ii)* $\mathbf{val}(\mathbf{apply}(n)(m)) = \mathbf{val}(n)(\mathbf{val}(m))$.

As a principal application of the Enumeration Theorem we may mention the following: suppose $u$ is given as LAMBDA-definable. We look at its definition and rewrite it in terms of combinators—eventually in terms of $\mathbf{G}$ alone. Then using 0 and $\mathbf{apply}$ we write down the name of an integer corresponding to the combination—say, $n$. By Theorem 3.2 we see that we have *effectively found* from
the definition an integer such that $\mathbf{val}\, n = u$. This remark can be strengthened by some numerology.

$$(3.8) \quad \mathbf{apply}(0)(0) = 1 \quad \text{and} \quad \mathbf{val}(1) = 0;$$

$$(3.9) \quad \mathbf{apply}(0)(1) = 3 \quad \text{and} \quad \mathbf{val}(3) = \langle \mathbf{suc}, \ldots \rangle;$$

$$(3.10) \quad \mathbf{apply}(3)(1) = 12 \quad \text{and} \quad \mathbf{val}(12) = \mathbf{suc}.$$

Thus, define $\mathbf{num}$ as the least fixed point:

$$(3.11) \quad \mathbf{num} = \lambda n \in \omega.\, n \supset 1,\, \mathbf{apply}(12)(\mathbf{num}(n - 1)),$$

and derive the equation for all $n \in \omega$:

$$(3.12) \quad \mathbf{val}(\mathbf{num}(n)) = n.$$

We note that $\mathbf{num}$ is a primitive recursive (total) function. The combinator $\mathbf{num}$ allows us now to effectively find a LAMBDA-definition, corresponding to a given LAMBDA-definable element $u$, of an element $v$ such that uniformly in the integer variable $n$ we have $\mathbf{val}(v(n)) = u(n)$. Further, $v$ is a primitive recursive (total) function. This is the technique involved in the proof of Kleene's well-known result:

**THEOREM 3.3 (The second recursion theorem).** Take a LAMBDA-definable element $v$ such that:

*(i)* $\mathbf{val}(v(n)) = \lambda m \in \omega.\, \mathbf{val}(n)(\mathbf{apply}(m)(\mathbf{num}(m)))$,

and then define a combinator by:

*(ii)* $\mathbf{rec} = \lambda n \in \omega.\, \mathbf{apply}(v(n))(\mathbf{num}(v(n)))$.

Then we have a primitive recursive function with this fixed-point property:

*(iii)* $\mathbf{val}(\mathbf{rec}(n)) = \mathbf{val}(n)(\mathbf{rec}(n))$.

Note that if $u$ is LAMBDA-definable, then we find first an $n$ such that $\mathbf{val}(n) = u$. Next we calculate $k = \mathbf{rec}(n)$. This effectively gives us an integer such that $\mathbf{val}(k) = u(k)$. Gödel numbers represent expressions (combinations in $\mathbf{G}$), and $\mathbf{val}$ maps the numbers to the values denoted by the expressions in the model. The $k$ just found thus represents an expression whose value is defined in terms of its own Gödel number. In recursion theory there are many applications of this result. Another familiar argument shows:

**THEOREM 3.4 (The incompleteness theorem).** The set of integers $n$ such that $\mathbf{val}(n) = \bot$ is not r.e.; hence, there can be no effectively given formal system for enumerating all true equations between LAMBDA-terms.

(A critic may sense here an application of Church's thesis in stating the metatheoretic consequence of the nonresult.) A few details of the proof can be given to see how the notation works. First let $v$ be a (total) primitive recursive function such that:

$$\mathbf{val}(v(n)) = n \cap \mathbf{val}(n),$$

and note that:

$$n \cap \mathbf{val}(n) = \bot \quad \text{iff} \quad n \notin \mathbf{val}(n).$$

Call the set in question in Theorem 3.4 the set $b$. If it were r.e., then so would be:

$$\{n \in \omega \mid v(n) \in b\} = (\lambda n \in \omega.\, v(n) \cap b \supset n, n)(\top).$$

That would mean having an integer $k$ such that:

$$\mathbf{val}(k) = \{n \in \omega \mid v(n) \in b\}.$$

But then:

$$
\begin{aligned}
k \in \mathbf{val}(k) &\iff v(k) \in b \\
&\iff \mathbf{val}(v(k)) = \bot \\
&\iff k \notin \mathbf{val}(k),
\end{aligned}
$$

which gives us a contradiction. This is the usual diagonal argument.

The relationship $\mathbf{val}(n) = \mathbf{val}(m)$ means that the expressions with Gödel numbers $n$ and $m$ have the same value in the model. (This is not only not r.e. but is a complete $\Pi_2^0$-predicate.) A *total* mapping can be regarded as a *syntactical* transformation on expressions defined via Gödel numbers. Such a mapping $p$ is called *extensional* if it has the property:

$$\mathbf{val}(p(n)) = \mathbf{val}(p(m)) \quad \text{whenever} \quad \mathbf{val}(n) = \mathbf{val}(m).$$

The Myhill–Shepherdson theorem shows that extensional, syntactical mappings really depend on the *values* of the expressions. Precisely we have:

**THEOREM 3.5 (The completeness theorem for definability).** *If a (total) extensional mapping $p$ is LAMBDA-definable, then there is a LAMBDA-definable $q$ such that $\mathbf{val}(p(n)) = q(\mathbf{val}(n))$ for all $n \in \omega$.*

Of course $q$ is uniquely determined (because the values of $q$ are given at least on the finite sets). Thus any attempt to define something *new* by means of some strange mapping on Gödel numbers is bound to fail as long as it is *effective* and *extensional*. The main part of the argument is concentrated on showing these mappings to be *continuous*; that is why $q$ exists.

The preceding results indicate that the expected results on r.e. sets are forthcoming in a smooth and unified manner in this setting. Some knowledge of r.e. theory was presupposed, but analysis shows that the knowledge required is slight. The notion of primitive recursive functions should certainly be well understood together with standard examples. Partial functions need not be introduced separately since they are naturally incorporated into LAMBDA (the theory of multiple-valued functions). As a working definition of r.e. one can take either “empty or the range of a primitive recursive function” or, more uniformly, “a set of the form $\{m \mid \exists n.\, m + 1 = p(n)\}$ where $p$ is primitive recursive”. A few obvious closure properties of r.e. sets should then be proved, and then an adequate foundation for the discussion of LAMBDA will have been provided.

The point of introducing LAMBDA is that further closure properties are more easily expressed in a theory where equations can be variously interpreted as involving numbers, functionals, etc., without becoming too heavily involved in intricate Gödel numbering and encodings. Another useful feature of the present theory concerns the ease with which we can introduce *relative recursiveness*.
As we have seen, $\{\mathbf{val}(n) \mid n \in \omega\}$ is an enumeration of all r.e. sets. Suppose we add a new set $a$ as a new constant. What are the sets enumerable in $a$? Answer: $\{\mathbf{val}(n)(a) \mid n \in \omega\}$, since in combinatory logic a parameter can always be factored out as an extra argument. Another way to put the point is this: for $b$ to be enumeration reducible to $a$ it is necessary and sufficient that $b = u(a)$ where $u \in \mathbf{RE}$. This is *word for word* the definition given by Rogers (1967, pp. 146–147). What we have done is to put the theory of enumeration operators (Friedberg–Rogers and Myhill–Shepherdson) into a general setting in which the language LAMBDA not only provides definitions but also the basis of a calculus for demonstrating properties of the operators defined. The algebraic style of this language throws a little light on the notion of enumeration degree. In the first place we can identify the degree of an element with the set of all objects reducible to it (rather than just those equivalent to it) and write

$$\mathbf{Deg}(a) = \{u(a) \mid u \in \mathbf{RE}\}.$$

The set-theoretical inclusion is then the same as the partial ordering of degrees. What kind of a partially ordered set do we have?

**THEOREM 3.6 (The subalgebra theorem).** *The enumeration degrees are exactly the finitely generated combinatory subalgebras of* $\mathbf{P}\omega$.

By “subalgebras” here we of course mean subsets containing $\mathbf{G}$ and closed under application (hence, they contain all of $\mathbf{RE}$, the least subalgebra). Part of the assertion is that every finitely generated subalgebra has a single generator (under application). This fact is an easy extension of Theorem 3.1. Not very much seems to be known about enumeration degrees. Joins can obviously be formed using the pairing function $\langle x, y \rangle$ on sets. Each degree is a countable set; hence, it is trivial to obtain the existence of a sequence of degrees whose *infinite join* is not a degree (not finitely generated). The intersection of subalgebras is a subalgebra—but it may not be a degree even starting with degrees. There are no minimal degrees above $\mathbf{RE}$, but there are minimal *pairs* of degrees. Also for a given degree there are only countably many degrees minimal over it; but the question of whether the partial ordering of enumeration degrees is dense seems still to be open.

Theorem 3.6 shows that the semilattice of enumeration degrees is naturally extendable to a *complete lattice* (the lattice of all subalgebras of $\mathbf{P}\omega$), but whether there is anything interesting to say about this complete lattice from the point of view of structure is not at all clear. Rogers has shown (1967, pp. 151–153) that Turing degrees can be defined in terms of enumeration degrees by restricting to special elements. In our style of notation we would define the space:

$$\mathbf{TOT} = \{u \mid u = \mathbf{\$}(u) \text{ and } \forall n \in \omega.\, u(n) \in \omega\},$$

the space of all graphs of total functions. Then the system $\{\mathbf{Deg}(u) \mid u \in \mathbf{TOT}\}$ is isomorphic to the system of Turing degrees. Now there are many other interesting subsets of $\mathbf{P}\omega$. Whether the degree structure of these various subsets is worth investigation is a question whose answer awaits some new ideas.

Among the subsets of $\mathbf{P}\omega$ with natural mathematical structure, we of course have $\mathbf{FUN}$, which is a semigroup under $\circ = \lambda u \lambda v \lambda x.\, u(v(x))$. It is, however, a rather complicated semigroup. We introduce for its study three new combinators:

$$(3.13) \quad \mathbf{R} = \lambda x.\, \langle 0, x \rangle;$$

$$(3.14) \quad \mathbf{L} = \lambda x.\, x_1(x_2);$$

$$(3.15) \quad \bar{u} = \lambda x.\, x_0 \supset \langle 1, u, x_1 \rangle,\, \overline{u(x_1)(x_2)}.$$

**THEOREM 3.7 (The semigroup theorem).** The countable semigroup $\mathbf{RE} \cap \mathbf{FUN}$ of computable enumeration operators is finitely generated by $\mathbf{R}$, $\mathbf{L}$ and $\bar{\mathbf{G}}$.

The proof rests on the verification of two equations which permit an application of Theorem 3.1:

$$(3.16) \quad \mathbf{L} \circ \bar{u} \circ \mathbf{R} = \lambda x.\, u(x)$$

$$(3.17) \quad \bar{u} \circ \bar{v} \circ \mathbf{R} = \overline{u(v)}.$$

Certainly the word problem for $\mathbf{RE} \cap \mathbf{FUN}$ is unsolvable, indeed, not even recursively enumerable. Can the semigroup be generated by *two* generators by the way?
