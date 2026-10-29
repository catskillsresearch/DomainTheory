# Theorem 8.5

**THEOREM 8.5.** For an approximable mapping $a : E \to E$ the following are equivalent:

(i) $a$ is a finitary projection;

(ii) $a(x) = \{Y \in E \mid \exists X \in x.\, X \subseteq Y \land X \ a \ X\}$, for all $x \in |E|$.

*Proof:* Suppose $a$ satisfies (ii) first. Inasmuch as $X \in x$ and $X \subseteq Y$ always imply $Y \in x$, for all $x \in |E|$, we see $a(x) \subseteq x$ must always hold. Moreover, it is obvious that $X \in x$ and $X \ a \ X$ always imply $X \in a(x)$; therefore, $a(x) \subseteq a(a(x))$ for all $x \in |E|$. This shows that $a$

<!-- page 138 -->

is indeed a projection.

Let $D = \{X \in E \mid X \ a \ X\}$, then it is easy to check that $D \triangleleft E$ and that $a$ is determined from $D$ exactly as in 8.2; thus, the fixed-point set of $a$ is isomorphic to a domain, by what we have already proved. So we have shown (ii) implies (i).

In the converse direction, assume that $a$ is a finitary projection. And let the system $D$ be isomorphic to the fixed-point set of $a$. We have the situation of Theorem 6.15. There is a projection pair,

$$i : D \to E \quad \text{and} \quad j : E \to D,$$

where the connection with $a$ gives:

$$j \circ i = I_D \quad \text{and} \quad i \circ j = a \subseteq I_E.$$

By 6.15, $D \cong D' \triangleleft E$, and we want to identify $D'$ in terms of $a$ as follows:

$$D' = \{X \in E \mid X \ a \ X\}.$$

Now from a reading of the proof of 6.15 the neighbourhoods of $D'$ are just those corresponding to the finite elements of $D$. But any such element is a fixed point of $a$. We have

$$X \in D' \quad \text{implies} \quad a(\uparrow X) = \uparrow X \quad \text{implies} \quad X \ a \ X.$$

Conversely, if $X \ a \ X$ holds, then $\uparrow X \subseteq a(\uparrow X)$. But $a$ is a projection, so $\uparrow X$ is a fixed point. But $i(j(\uparrow X)) = \uparrow X$ means $j(\uparrow X)$ is a finite element of $|D|$. So $X \in D'$, and we have $D'$ identified as desired.

Finally, if we calculate $a = i \circ j$ by the formulae of 6.12 (with $D'$ for $D$, of course), we obtain our formula (ii). $\square$

The criterion for being a finitary projection just obtained provides us with a very interesting new combinator.

**[Theorem_8_5.lean](Theorem_8_5.lean)**

@import "Theorem_8_5.lean"
