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

**Lean 4**

- [DataTypesAsLattices/Enumeration.lean](DomainTheory/DataTypesAsLattices/Enumeration.lean)
- [DataTypesAsLattices/Enumeration/Avoids.lean](DomainTheory/DataTypesAsLattices/Enumeration/Avoids.lean)
- [DataTypesAsLattices/Enumeration/Basic.lean](DomainTheory/DataTypesAsLattices/Enumeration/Basic.lean)
- [DataTypesAsLattices/Enumeration/BasicInst85.lean](DomainTheory/DataTypesAsLattices/Enumeration/BasicInst85.lean)
- [DataTypesAsLattices/Enumeration/Deg.lean](DomainTheory/DataTypesAsLattices/Enumeration/Deg.lean)
- [DataTypesAsLattices/Enumeration/Deg_isSubalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/Deg_isSubalgebra.lean)
- [DataTypesAsLattices/Enumeration/Deg_self.lean](DomainTheory/DataTypesAsLattices/Enumeration/Deg_self.lean)
- [DataTypesAsLattices/Enumeration/Gbar.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gbar.lean)
- [DataTypesAsLattices/Enumeration/Gbar_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gbar_combinatory.lean)
- [DataTypesAsLattices/Enumeration/Gbar_mem_FUN.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gbar_mem_FUN.lean)
- [DataTypesAsLattices/Enumeration/Gcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb.lean)
- [DataTypesAsLattices/Enumeration/Gcomb_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb_app.lean)
- [DataTypesAsLattices/Enumeration/Gcomb_app_self.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb_app_self.lean)
- [DataTypesAsLattices/Enumeration/Gcomb_bot.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb_bot.lean)
- [DataTypesAsLattices/Enumeration/Gcomb_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb_combinatory.lean)
- [DataTypesAsLattices/Enumeration/Gcomb_eq_condC.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb_eq_condC.lean)
- [DataTypesAsLattices/Enumeration/Gcomb_isRE.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb_isRE.lean)
- [DataTypesAsLattices/Enumeration/Gcomb_succ.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb_succ.lean)
- [DataTypesAsLattices/Enumeration/Gcomb_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gcomb_zero.lean)
- [DataTypesAsLattices/Enumeration/GeneratedFromG.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedFromG.lean)
- [DataTypesAsLattices/Enumeration/GeneratedSemigroup.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedSemigroup.lean)
- [DataTypesAsLattices/Enumeration/GeneratedSubalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedSubalgebra.lean)
- [DataTypesAsLattices/Enumeration/GeneratedSubalgebra_generator.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedSubalgebra_generator.lean)
- [DataTypesAsLattices/Enumeration/GeneratedSubalgebra_isSubalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/GeneratedSubalgebra_isSubalgebra.lean)
- [DataTypesAsLattices/Enumeration/Gpack.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gpack.lean)
- [DataTypesAsLattices/Enumeration/Gpack_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gpack_combinatory.lean)
- [DataTypesAsLattices/Enumeration/Gpack_ne_bot.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gpack_ne_bot.lean)
- [DataTypesAsLattices/Enumeration/Gpack_one.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gpack_one.lean)
- [DataTypesAsLattices/Enumeration/Gpack_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/Gpack_zero.lean)
- [DataTypesAsLattices/Enumeration/Icomb_SK.lean](DomainTheory/DataTypesAsLattices/Enumeration/Icomb_SK.lean)
- [DataTypesAsLattices/Enumeration/Icomb_SK_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/Icomb_SK_app.lean)
- [DataTypesAsLattices/Enumeration/IsExtensional.lean](DomainTheory/DataTypesAsLattices/Enumeration/IsExtensional.lean)
- [DataTypesAsLattices/Enumeration/IsSubalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/IsSubalgebra.lean)
- [DataTypesAsLattices/Enumeration/Kcomb_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/Kcomb_from_G.lean)
- [DataTypesAsLattices/Enumeration/Lcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lcomb.lean)
- [DataTypesAsLattices/Enumeration/Lcomb_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lcomb_app.lean)
- [DataTypesAsLattices/Enumeration/Lcomb_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lcomb_combinatory.lean)
- [DataTypesAsLattices/Enumeration/Lcomb_mem_FUN.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lcomb_mem_FUN.lean)
- [DataTypesAsLattices/Enumeration/Lterm.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lterm.lean)
- [DataTypesAsLattices/Enumeration/Lterm_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/Lterm_interp.lean)
- [DataTypesAsLattices/Enumeration/RE.lean](DomainTheory/DataTypesAsLattices/Enumeration/RE.lean)
- [DataTypesAsLattices/Enumeration/REPredu2eexists_param.lean](DomainTheory/DataTypesAsLattices/Enumeration/REPredu2eexists_param.lean)
- [DataTypesAsLattices/Enumeration/Rcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/Rcomb.lean)
- [DataTypesAsLattices/Enumeration/Rcomb_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/Rcomb_app.lean)
- [DataTypesAsLattices/Enumeration/Rcomb_app_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/Rcomb_app_zero.lean)
- [DataTypesAsLattices/Enumeration/Rcomb_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/Rcomb_combinatory.lean)
- [DataTypesAsLattices/Enumeration/Rcomb_mem_FUN.lean](DomainTheory/DataTypesAsLattices/Enumeration/Rcomb_mem_FUN.lean)
- [DataTypesAsLattices/Enumeration/Rterm.lean](DomainTheory/DataTypesAsLattices/Enumeration/Rterm.lean)
- [DataTypesAsLattices/Enumeration/Rterm_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/Rterm_interp.lean)
- [DataTypesAsLattices/Enumeration/Scomb_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/Scomb_from_G.lean)
- [DataTypesAsLattices/Enumeration/TOT.lean](DomainTheory/DataTypesAsLattices/Enumeration/TOT.lean)
- [DataTypesAsLattices/Enumeration/ValTrace.lean](DomainTheory/DataTypesAsLattices/Enumeration/ValTrace.lean)
- [DataTypesAsLattices/Enumeration/Ycode.lean](DomainTheory/DataTypesAsLattices/Enumeration/Ycode.lean)
- [DataTypesAsLattices/Enumeration/applyNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/applyNat.lean)
- [DataTypesAsLattices/Enumeration/argNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/argNat.lean)
- [DataTypesAsLattices/Enumeration/barComb.lean](DomainTheory/DataTypesAsLattices/Enumeration/barComb.lean)
- [DataTypesAsLattices/Enumeration/barComb_app2.lean](DomainTheory/DataTypesAsLattices/Enumeration/barComb_app2.lean)
- [DataTypesAsLattices/Enumeration/barComb_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/barComb_combinatory.lean)
- [DataTypesAsLattices/Enumeration/barComb_on_R.lean](DomainTheory/DataTypesAsLattices/Enumeration/barComb_on_R.lean)
- [DataTypesAsLattices/Enumeration/barComb_on_barPos_R.lean](DomainTheory/DataTypesAsLattices/Enumeration/barComb_on_barPos_R.lean)
- [DataTypesAsLattices/Enumeration/barPos.lean](DomainTheory/DataTypesAsLattices/Enumeration/barPos.lean)
- [DataTypesAsLattices/Enumeration/barPosTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/barPosTerm.lean)
- [DataTypesAsLattices/Enumeration/barPosTerm_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/barPosTerm_interp.lean)
- [DataTypesAsLattices/Enumeration/barPos_isScottContinuous_u.lean](DomainTheory/DataTypesAsLattices/Enumeration/barPos_isScottContinuous_u.lean)
- [DataTypesAsLattices/Enumeration/barPos_isScottContinuous_x.lean](DomainTheory/DataTypesAsLattices/Enumeration/barPos_isScottContinuous_x.lean)
- [DataTypesAsLattices/Enumeration/barPos_one.lean](DomainTheory/DataTypesAsLattices/Enumeration/barPos_one.lean)
- [DataTypesAsLattices/Enumeration/barPos_two.lean](DomainTheory/DataTypesAsLattices/Enumeration/barPos_two.lean)
- [DataTypesAsLattices/Enumeration/barPos_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/barPos_zero.lean)
- [DataTypesAsLattices/Enumeration/barStep.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStep.lean)
- [DataTypesAsLattices/Enumeration/barStepBody.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStepBody.lean)
- [DataTypesAsLattices/Enumeration/barStepBody_isScottContinuous_B.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStepBody_isScottContinuous_B.lean)
- [DataTypesAsLattices/Enumeration/barStepBody_isScottContinuous_u.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStepBody_isScottContinuous_u.lean)
- [DataTypesAsLattices/Enumeration/barStepBody_isScottContinuous_x.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStepBody_isScottContinuous_x.lean)
- [DataTypesAsLattices/Enumeration/barStepTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStepTerm.lean)
- [DataTypesAsLattices/Enumeration/barStepTerm_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStepTerm_interp.lean)
- [DataTypesAsLattices/Enumeration/barStep_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStep_app.lean)
- [DataTypesAsLattices/Enumeration/barStep_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/barStep_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/bar_generated.lean](DomainTheory/DataTypesAsLattices/Enumeration/bar_generated.lean)
- [DataTypesAsLattices/Enumeration/beforeHalt.lean](DomainTheory/DataTypesAsLattices/Enumeration/beforeHalt.lean)
- [DataTypesAsLattices/Enumeration/bitList.lean](DomainTheory/DataTypesAsLattices/Enumeration/bitList.lean)
- [DataTypesAsLattices/Enumeration/botCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/botCode.lean)
- [DataTypesAsLattices/Enumeration/bot_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/bot_combinatory.lean)
- [DataTypesAsLattices/Enumeration/combinatory_mem_Deg.lean](DomainTheory/DataTypesAsLattices/Enumeration/combinatory_mem_Deg.lean)
- [DataTypesAsLattices/Enumeration/combinatory_mem_subalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/combinatory_mem_subalgebra.lean)
- [DataTypesAsLattices/Enumeration/condC_app2.lean](DomainTheory/DataTypesAsLattices/Enumeration/condC_app2.lean)
- [DataTypesAsLattices/Enumeration/condC_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/condC_from_G.lean)
- [DataTypesAsLattices/Enumeration/condClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/condClosed.lean)
- [DataTypesAsLattices/Enumeration/condClosed_avoids8.lean](DomainTheory/DataTypesAsLattices/Enumeration/condClosed_avoids8.lean)
- [DataTypesAsLattices/Enumeration/condClosed_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/condClosed_interp.lean)
- [DataTypesAsLattices/Enumeration/condCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/condCode.lean)
- [DataTypesAsLattices/Enumeration/condSet_same.lean](DomainTheory/DataTypesAsLattices/Enumeration/condSet_same.lean)
- [DataTypesAsLattices/Enumeration/cond_graph_eq_bot_iff.lean](DomainTheory/DataTypesAsLattices/Enumeration/cond_graph_eq_bot_iff.lean)
- [DataTypesAsLattices/Enumeration/diagonalInterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/diagonalInterCode.lean)
- [DataTypesAsLattices/Enumeration/e_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/e_combinatory.lean)
- [DataTypesAsLattices/Enumeration/e_eq_unionBits.lean](DomainTheory/DataTypesAsLattices/Enumeration/e_eq_unionBits.lean)
- [DataTypesAsLattices/Enumeration/e_subset_ofNat_iff.lean](DomainTheory/DataTypesAsLattices/Enumeration/e_subset_ofNat_iff.lean)
- [DataTypesAsLattices/Enumeration/enumBottomTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumBottomTerm.lean)
- [DataTypesAsLattices/Enumeration/enumBottomTerm_avoids.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumBottomTerm_avoids.lean)
- [DataTypesAsLattices/Enumeration/enumBottomTerm_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumBottomTerm_interp.lean)
- [DataTypesAsLattices/Enumeration/enumComp.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumComp.lean)
- [DataTypesAsLattices/Enumeration/enumComp_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumComp_app.lean)
- [DataTypesAsLattices/Enumeration/enumComp_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumComp_combinatory.lean)
- [DataTypesAsLattices/Enumeration/enumComp_eq_compose.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumComp_eq_compose.lean)
- [DataTypesAsLattices/Enumeration/enumComp_mem_FUN.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumComp_mem_FUN.lean)
- [DataTypesAsLattices/Enumeration/enumerationUnion_left_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumerationUnion_left_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/enumerationUnion_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/enumerationUnion_right_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/eq_3_1.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_1.lean)
- [DataTypesAsLattices/Enumeration/eq_3_10_apply.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_10_apply.lean)
- [DataTypesAsLattices/Enumeration/eq_3_10_val.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_10_val.lean)
- [DataTypesAsLattices/Enumeration/eq_3_12.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_12.lean)
- [DataTypesAsLattices/Enumeration/eq_3_15.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_15.lean)
- [DataTypesAsLattices/Enumeration/eq_3_16.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_16.lean)
- [DataTypesAsLattices/Enumeration/eq_3_16_bar.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_16_bar.lean)
- [DataTypesAsLattices/Enumeration/eq_3_16_operator.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_16_operator.lean)
- [DataTypesAsLattices/Enumeration/eq_3_17.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_17.lean)
- [DataTypesAsLattices/Enumeration/eq_3_17_projections.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_17_projections.lean)
- [DataTypesAsLattices/Enumeration/eq_3_17_semigroup.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_17_semigroup.lean)
- [DataTypesAsLattices/Enumeration/eq_3_2.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_2.lean)
- [DataTypesAsLattices/Enumeration/eq_3_5.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_5.lean)
- [DataTypesAsLattices/Enumeration/eq_3_6.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_6.lean)
- [DataTypesAsLattices/Enumeration/eq_3_8_apply.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_8_apply.lean)
- [DataTypesAsLattices/Enumeration/eq_3_8_val.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_8_val.lean)
- [DataTypesAsLattices/Enumeration/eq_3_9_apply.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_9_apply.lean)
- [DataTypesAsLattices/Enumeration/eq_3_9_val.lean](DomainTheory/DataTypesAsLattices/Enumeration/eq_3_9_val.lean)
- [DataTypesAsLattices/Enumeration/exists_concat_traces.lean](DomainTheory/DataTypesAsLattices/Enumeration/exists_concat_traces.lean)
- [DataTypesAsLattices/Enumeration/exists_triangle_succ.lean](DomainTheory/DataTypesAsLattices/Enumeration/exists_triangle_succ.lean)
- [DataTypesAsLattices/Enumeration/filterC.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterC.lean)
- [DataTypesAsLattices/Enumeration/filterC_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterC_app.lean)
- [DataTypesAsLattices/Enumeration/filterC_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterC_combinatory.lean)
- [DataTypesAsLattices/Enumeration/filterEnv.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterEnv.lean)
- [DataTypesAsLattices/Enumeration/filterEnv_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterEnv_combinatory.lean)
- [DataTypesAsLattices/Enumeration/filterNum.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterNum.lean)
- [DataTypesAsLattices/Enumeration/filterOp.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterOp.lean)
- [DataTypesAsLattices/Enumeration/filterRealizer.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterRealizer.lean)
- [DataTypesAsLattices/Enumeration/filterRealizer_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterRealizer_combinatory.lean)
- [DataTypesAsLattices/Enumeration/filterRealizer_realizes.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterRealizer_realizes.lean)
- [DataTypesAsLattices/Enumeration/filterSeq_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterSeq_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/filterTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/filterTerm.lean)
- [DataTypesAsLattices/Enumeration/fin.lean](DomainTheory/DataTypesAsLattices/Enumeration/fin.lean)
- [DataTypesAsLattices/Enumeration/finAux.lean](DomainTheory/DataTypesAsLattices/Enumeration/finAux.lean)
- [DataTypesAsLattices/Enumeration/funOf_ofNat_mem_re.lean](DomainTheory/DataTypesAsLattices/Enumeration/funOf_ofNat_mem_re.lean)
- [DataTypesAsLattices/Enumeration/funRetractTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/funRetractTerm.lean)
- [DataTypesAsLattices/Enumeration/funRetractTerm_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/funRetractTerm_interp.lean)
- [DataTypesAsLattices/Enumeration/funRetract_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/funRetract_combinatory.lean)
- [DataTypesAsLattices/Enumeration/gClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/gClosed.lean)
- [DataTypesAsLattices/Enumeration/gClosed_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/gClosed_interp.lean)
- [DataTypesAsLattices/Enumeration/generatedSemigroup_mem_RE_FUN.lean](DomainTheory/DataTypesAsLattices/Enumeration/generatedSemigroup_mem_RE_FUN.lean)
- [DataTypesAsLattices/Enumeration/generators_mem_singleGenerator_degree.lean](DomainTheory/DataTypesAsLattices/Enumeration/generators_mem_singleGenerator_degree.lean)
- [DataTypesAsLattices/Enumeration/gpackClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/gpackClosed.lean)
- [DataTypesAsLattices/Enumeration/gpackClosed_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/gpackClosed_interp.lean)
- [DataTypesAsLattices/Enumeration/graph_mem_FUN.lean](DomainTheory/DataTypesAsLattices/Enumeration/graph_mem_FUN.lean)
- [DataTypesAsLattices/Enumeration/haltEnum.lean](DomainTheory/DataTypesAsLattices/Enumeration/haltEnum.lean)
- [DataTypesAsLattices/Enumeration/haltEnum_range_not_computable.lean](DomainTheory/DataTypesAsLattices/Enumeration/haltEnum_range_not_computable.lean)
- [DataTypesAsLattices/Enumeration/haltEnum_range_re.lean](DomainTheory/DataTypesAsLattices/Enumeration/haltEnum_range_re.lean)
- [DataTypesAsLattices/Enumeration/haltEnum_succ_iff.lean](DomainTheory/DataTypesAsLattices/Enumeration/haltEnum_succ_iff.lean)
- [DataTypesAsLattices/Enumeration/interC_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/interC_combinatory.lean)
- [DataTypesAsLattices/Enumeration/interCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/interCode.lean)
- [DataTypesAsLattices/Enumeration/interStepTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/interStepTerm.lean)
- [DataTypesAsLattices/Enumeration/interStepTerm_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/interStepTerm_interp.lean)
- [DataTypesAsLattices/Enumeration/interp_avoids.lean](DomainTheory/DataTypesAsLattices/Enumeration/interp_avoids.lean)
- [DataTypesAsLattices/Enumeration/kClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/kClosed.lean)
- [DataTypesAsLattices/Enumeration/kClosed_avoids8.lean](DomainTheory/DataTypesAsLattices/Enumeration/kClosed_avoids8.lean)
- [DataTypesAsLattices/Enumeration/kClosed_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/kClosed_interp.lean)
- [DataTypesAsLattices/Enumeration/mem_funOf_ofNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/mem_funOf_ofNat.lean)
- [DataTypesAsLattices/Enumeration/mem_myhillQ.lean](DomainTheory/DataTypesAsLattices/Enumeration/mem_myhillQ.lean)
- [DataTypesAsLattices/Enumeration/myhillCase1Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillCase1Code.lean)
- [DataTypesAsLattices/Enumeration/myhillCase2Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillCase2Code.lean)
- [DataTypesAsLattices/Enumeration/myhillFilterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillFilterCode.lean)
- [DataTypesAsLattices/Enumeration/myhillQ.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillQ.lean)
- [DataTypesAsLattices/Enumeration/myhillQ_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillQ_app.lean)
- [DataTypesAsLattices/Enumeration/myhillQ_isRE.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillQ_isRE.lean)
- [DataTypesAsLattices/Enumeration/myhillRealizer.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillRealizer.lean)
- [DataTypesAsLattices/Enumeration/myhillRealizer_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/myhillRealizer_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/not_mem_zero_Gcomb.lean](DomainTheory/DataTypesAsLattices/Enumeration/not_mem_zero_Gcomb.lean)
- [DataTypesAsLattices/Enumeration/not_mem_zero_cond_graph.lean](DomainTheory/DataTypesAsLattices/Enumeration/not_mem_zero_cond_graph.lean)
- [DataTypesAsLattices/Enumeration/num.lean](DomainTheory/DataTypesAsLattices/Enumeration/num.lean)
- [DataTypesAsLattices/Enumeration/opNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/opNat.lean)
- [DataTypesAsLattices/Enumeration/packList.lean](DomainTheory/DataTypesAsLattices/Enumeration/packList.lean)
- [DataTypesAsLattices/Enumeration/packList_components_mem_Deg.lean](DomainTheory/DataTypesAsLattices/Enumeration/packList_components_mem_Deg.lean)
- [DataTypesAsLattices/Enumeration/packList_cons_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/packList_cons_zero.lean)
- [DataTypesAsLattices/Enumeration/packList_mem_subalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/packList_mem_subalgebra.lean)
- [DataTypesAsLattices/Enumeration/predC_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/predC_from_G.lean)
- [DataTypesAsLattices/Enumeration/predClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/predClosed.lean)
- [DataTypesAsLattices/Enumeration/predClosed_avoids8.lean](DomainTheory/DataTypesAsLattices/Enumeration/predClosed_avoids8.lean)
- [DataTypesAsLattices/Enumeration/predClosed_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/predClosed_interp.lean)
- [DataTypesAsLattices/Enumeration/primrecPred_beforeHalt.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecPred_beforeHalt.lean)
- [DataTypesAsLattices/Enumeration/primrecPred_valEntryJustified.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecPred_valEntryJustified.lean)
- [DataTypesAsLattices/Enumeration/primrecPred_valTraceStruct.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecPred_valTraceStruct.lean)
- [DataTypesAsLattices/Enumeration/primrecRel_valTraceHas.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecRel_valTraceHas.lean)
- [DataTypesAsLattices/Enumeration/primrec_applyNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_applyNat.lean)
- [DataTypesAsLattices/Enumeration/primrec_diagonalInterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_diagonalInterCode.lean)
- [DataTypesAsLattices/Enumeration/primrec_filterNum.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_filterNum.lean)
- [DataTypesAsLattices/Enumeration/primrec_fin.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_fin.lean)
- [DataTypesAsLattices/Enumeration/primrec_haltEnum.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_haltEnum.lean)
- [DataTypesAsLattices/Enumeration/primrec_myhillCase1Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_myhillCase1Code.lean)
- [DataTypesAsLattices/Enumeration/primrec_myhillCase2Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_myhillCase2Code.lean)
- [DataTypesAsLattices/Enumeration/primrec_myhillFilterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_myhillFilterCode.lean)
- [DataTypesAsLattices/Enumeration/primrec_num.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_num.lean)
- [DataTypesAsLattices/Enumeration/primrec_recNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_recNat.lean)
- [DataTypesAsLattices/Enumeration/primrec_secondRecSubst.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_secondRecSubst.lean)
- [DataTypesAsLattices/Enumeration/primrec_secondRecV.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_secondRecV.lean)
- [DataTypesAsLattices/Enumeration/primrec_triangle.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_triangle.lean)
- [DataTypesAsLattices/Enumeration/primrec_unpairComp.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_unpairComp.lean)
- [DataTypesAsLattices/Enumeration/primrec_unpairW.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrec_unpairW.lean)
- [DataTypesAsLattices/Enumeration/primrecu2082_finAux.lean](DomainTheory/DataTypesAsLattices/Enumeration/primrecu2082_finAux.lean)
- [DataTypesAsLattices/Enumeration/realizes_valNat_mem.lean](DomainTheory/DataTypesAsLattices/Enumeration/realizes_valNat_mem.lean)
- [DataTypesAsLattices/Enumeration/recCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/recCode.lean)
- [DataTypesAsLattices/Enumeration/recNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/recNat.lean)
- [DataTypesAsLattices/Enumeration/sClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/sClosed.lean)
- [DataTypesAsLattices/Enumeration/sClosed_avoids8.lean](DomainTheory/DataTypesAsLattices/Enumeration/sClosed_avoids8.lean)
- [DataTypesAsLattices/Enumeration/sClosed_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/sClosed_interp.lean)
- [DataTypesAsLattices/Enumeration/secondRecOperator.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecOperator.lean)
- [DataTypesAsLattices/Enumeration/secondRecOperatorCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecOperatorCode.lean)
- [DataTypesAsLattices/Enumeration/secondRecOperator_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecOperator_app.lean)
- [DataTypesAsLattices/Enumeration/secondRecOperator_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecOperator_combinatory.lean)
- [DataTypesAsLattices/Enumeration/secondRecSubst.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecSubst.lean)
- [DataTypesAsLattices/Enumeration/secondRecSubstC.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecSubstC.lean)
- [DataTypesAsLattices/Enumeration/secondRecSubstC_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecSubstC_combinatory.lean)
- [DataTypesAsLattices/Enumeration/secondRecSubstC_realizes.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecSubstC_realizes.lean)
- [DataTypesAsLattices/Enumeration/secondRecV.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecV.lean)
- [DataTypesAsLattices/Enumeration/secondRecVal.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecVal.lean)
- [DataTypesAsLattices/Enumeration/secondRecVal_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecVal_app.lean)
- [DataTypesAsLattices/Enumeration/secondRecVal_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/secondRecVal_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/seq2Term.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2Term.lean)
- [DataTypesAsLattices/Enumeration/seq2Term_avoids8.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2Term_avoids8.lean)
- [DataTypesAsLattices/Enumeration/seq2Term_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2Term_interp.lean)
- [DataTypesAsLattices/Enumeration/seq2_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_combinatory.lean)
- [DataTypesAsLattices/Enumeration/seq2_eq_SK.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_eq_SK.lean)
- [DataTypesAsLattices/Enumeration/seq2_left_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_left_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/seq2_mem_subalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_mem_subalgebra.lean)
- [DataTypesAsLattices/Enumeration/seq2_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/seq2_right_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/seqConsTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/seqConsTerm.lean)
- [DataTypesAsLattices/Enumeration/seqConsTerm_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/seqConsTerm_interp.lean)
- [DataTypesAsLattices/Enumeration/seqCons_right_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/seqCons_right_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/singleGenerator.lean](DomainTheory/DataTypesAsLattices/Enumeration/singleGenerator.lean)
- [DataTypesAsLattices/Enumeration/singleGenerator_app_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/singleGenerator_app_zero.lean)
- [DataTypesAsLattices/Enumeration/singleGenerator_mem_subalgebra.lean](DomainTheory/DataTypesAsLattices/Enumeration/singleGenerator_mem_subalgebra.lean)
- [DataTypesAsLattices/Enumeration/sucC_from_G.lean](DomainTheory/DataTypesAsLattices/Enumeration/sucC_from_G.lean)
- [DataTypesAsLattices/Enumeration/sucC_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/sucC_zero.lean)
- [DataTypesAsLattices/Enumeration/sucClosed.lean](DomainTheory/DataTypesAsLattices/Enumeration/sucClosed.lean)
- [DataTypesAsLattices/Enumeration/sucClosed_avoids8.lean](DomainTheory/DataTypesAsLattices/Enumeration/sucClosed_avoids8.lean)
- [DataTypesAsLattices/Enumeration/sucClosed_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/sucClosed_interp.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_1.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_1.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_2.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_2.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_2_i.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_2_i.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_2_range.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_2_range.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_2_surjective.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_2_surjective.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_3.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_3.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_3_from_v.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_3_from_v.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_3_i.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_3_i.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_3_ii.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_3_ii.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_3_val.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_3_val.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_4.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_4.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_4_diagonal.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_4_diagonal.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_4_re_diagonal.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_4_re_diagonal.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_5.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_5.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_5_case1.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_5_case1.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_5_case2.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_5_case2.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_5_of_realizer.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_5_of_realizer.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_5_q.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_5_q.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_5_q_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_5_q_app.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_5_unique.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_5_unique.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_6.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_6.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_6_converse.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_6_converse.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_6_degree.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_6_degree.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_6_finite.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_6_finite.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_6_generated.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_6_generated.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_7.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_7.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_7_equations.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_7_equations.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_7_generation.lean](DomainTheory/DataTypesAsLattices/Enumeration/theorem_3_7_generation.lean)
- [DataTypesAsLattices/Enumeration/unionBits.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionBits.lean)
- [DataTypesAsLattices/Enumeration/unionBits_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionBits_combinatory.lean)
- [DataTypesAsLattices/Enumeration/unionBits_eq.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionBits_eq.lean)
- [DataTypesAsLattices/Enumeration/unionCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionCode.lean)
- [DataTypesAsLattices/Enumeration/unionOperator_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionOperator_app.lean)
- [DataTypesAsLattices/Enumeration/unionOperator_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionOperator_combinatory.lean)
- [DataTypesAsLattices/Enumeration/unionTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionTerm.lean)
- [DataTypesAsLattices/Enumeration/unionTerm_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/unionTerm_interp.lean)
- [DataTypesAsLattices/Enumeration/union_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/union_combinatory.lean)
- [DataTypesAsLattices/Enumeration/unpairComp.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairComp.lean)
- [DataTypesAsLattices/Enumeration/unpairComp_eq.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairComp_eq.lean)
- [DataTypesAsLattices/Enumeration/unpairW.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairW.lean)
- [DataTypesAsLattices/Enumeration/unpairWRec.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairWRec.lean)
- [DataTypesAsLattices/Enumeration/unpairWRec_lt.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairWRec_lt.lean)
- [DataTypesAsLattices/Enumeration/unpairWRec_min.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairWRec_min.lean)
- [DataTypesAsLattices/Enumeration/unpairWRec_succ.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairWRec_succ.lean)
- [DataTypesAsLattices/Enumeration/unpairW_eq.lean](DomainTheory/DataTypesAsLattices/Enumeration/unpairW_eq.lean)
- [DataTypesAsLattices/Enumeration/vaalC.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalC.lean)
- [DataTypesAsLattices/Enumeration/vaalC_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalC_combinatory.lean)
- [DataTypesAsLattices/Enumeration/vaalC_computable.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalC_computable.lean)
- [DataTypesAsLattices/Enumeration/vaalC_fixedPoint.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalC_fixedPoint.lean)
- [DataTypesAsLattices/Enumeration/vaalC_typed.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalC_typed.lean)
- [DataTypesAsLattices/Enumeration/vaalC_unfold.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalC_unfold.lean)
- [DataTypesAsLattices/Enumeration/vaalF.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalF.lean)
- [DataTypesAsLattices/Enumeration/vaalF_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalF_app.lean)
- [DataTypesAsLattices/Enumeration/vaalF_body_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalF_body_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/vaalF_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalF_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/vaalStepTerm.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalStepTerm.lean)
- [DataTypesAsLattices/Enumeration/vaalStepTerm_interp.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalStepTerm_interp.lean)
- [DataTypesAsLattices/Enumeration/vaalTyped.lean](DomainTheory/DataTypesAsLattices/Enumeration/vaalTyped.lean)
- [DataTypesAsLattices/Enumeration/valC.lean](DomainTheory/DataTypesAsLattices/Enumeration/valC.lean)
- [DataTypesAsLattices/Enumeration/valC_valNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/valC_valNat.lean)
- [DataTypesAsLattices/Enumeration/valEntryJustified.lean](DomainTheory/DataTypesAsLattices/Enumeration/valEntryJustified.lean)
- [DataTypesAsLattices/Enumeration/valEntryJustified_mono.lean](DomainTheory/DataTypesAsLattices/Enumeration/valEntryJustified_mono.lean)
- [DataTypesAsLattices/Enumeration/valNat.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat.lean)
- [DataTypesAsLattices/Enumeration/valNat_Ycode.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_Ycode.lean)
- [DataTypesAsLattices/Enumeration/valNat_apply.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_apply.lean)
- [DataTypesAsLattices/Enumeration/valNat_botCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_botCode.lean)
- [DataTypesAsLattices/Enumeration/valNat_combinatory.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_combinatory.lean)
- [DataTypesAsLattices/Enumeration/valNat_condCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_condCode.lean)
- [DataTypesAsLattices/Enumeration/valNat_diagonalInterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_diagonalInterCode.lean)
- [DataTypesAsLattices/Enumeration/valNat_filterOp.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_filterOp.lean)
- [DataTypesAsLattices/Enumeration/valNat_fin.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_fin.lean)
- [DataTypesAsLattices/Enumeration/valNat_finAux.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_finAux.lean)
- [DataTypesAsLattices/Enumeration/valNat_interCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_interCode.lean)
- [DataTypesAsLattices/Enumeration/valNat_mem_comp_primrec.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_mem_comp_primrec.lean)
- [DataTypesAsLattices/Enumeration/valNat_mem_iff.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_mem_iff.lean)
- [DataTypesAsLattices/Enumeration/valNat_mem_re.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_mem_re.lean)
- [DataTypesAsLattices/Enumeration/valNat_myhillCase1Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_myhillCase1Code.lean)
- [DataTypesAsLattices/Enumeration/valNat_myhillCase2Code.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_myhillCase2Code.lean)
- [DataTypesAsLattices/Enumeration/valNat_myhillCase2Code_bot.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_myhillCase2Code_bot.lean)
- [DataTypesAsLattices/Enumeration/valNat_myhillCase2Code_ne_bot.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_myhillCase2Code_ne_bot.lean)
- [DataTypesAsLattices/Enumeration/valNat_myhillFilterCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_myhillFilterCode.lean)
- [DataTypesAsLattices/Enumeration/valNat_secondRecOperatorCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_secondRecOperatorCode.lean)
- [DataTypesAsLattices/Enumeration/valNat_succ.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_succ.lean)
- [DataTypesAsLattices/Enumeration/valNat_unionCode.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_unionCode.lean)
- [DataTypesAsLattices/Enumeration/valNat_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/valNat_zero.lean)
- [DataTypesAsLattices/Enumeration/valRank.lean](DomainTheory/DataTypesAsLattices/Enumeration/valRank.lean)
- [DataTypesAsLattices/Enumeration/valStage_eq_of_rank_le.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStage_eq_of_rank_le.lean)
- [DataTypesAsLattices/Enumeration/valStage_subset.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStage_subset.lean)
- [DataTypesAsLattices/Enumeration/valStep.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStep.lean)
- [DataTypesAsLattices/Enumeration/valStepValue.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStepValue.lean)
- [DataTypesAsLattices/Enumeration/valStep_app.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStep_app.lean)
- [DataTypesAsLattices/Enumeration/valStep_app_succ.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStep_app_succ.lean)
- [DataTypesAsLattices/Enumeration/valStep_app_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStep_app_zero.lean)
- [DataTypesAsLattices/Enumeration/valStep_body_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Enumeration/valStep_body_isScottContinuous.lean)
- [DataTypesAsLattices/Enumeration/valTraceG.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceG.lean)
- [DataTypesAsLattices/Enumeration/valTraceG_re.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceG_re.lean)
- [DataTypesAsLattices/Enumeration/valTraceHas.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceHas.lean)
- [DataTypesAsLattices/Enumeration/valTraceHas_append_left.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceHas_append_left.lean)
- [DataTypesAsLattices/Enumeration/valTraceHas_append_right.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceHas_append_right.lean)
- [DataTypesAsLattices/Enumeration/valTraceHas_iff.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceHas_iff.lean)
- [DataTypesAsLattices/Enumeration/valTraceOk.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk.lean)
- [DataTypesAsLattices/Enumeration/valTraceOk_append.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk_append.lean)
- [DataTypesAsLattices/Enumeration/valTraceOk_complete.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk_complete.lean)
- [DataTypesAsLattices/Enumeration/valTraceOk_cons.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk_cons.lean)
- [DataTypesAsLattices/Enumeration/valTraceOk_empty.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk_empty.lean)
- [DataTypesAsLattices/Enumeration/valTraceOk_re.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk_re.lean)
- [DataTypesAsLattices/Enumeration/valTraceOk_sound.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk_sound.lean)
- [DataTypesAsLattices/Enumeration/valTraceOk_zero.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceOk_zero.lean)
- [DataTypesAsLattices/Enumeration/valTraceStruct.lean](DomainTheory/DataTypesAsLattices/Enumeration/valTraceStruct.lean)
