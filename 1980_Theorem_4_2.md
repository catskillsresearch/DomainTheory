# Theorem 4.2

Because the element we have shown to exist in 4.1 is a least element, it is unique. That is, we have associated with each $f : D \to D$ a special element $x_f \in |D|$ determined by the choice of $f$. A function has therefore been defined mapping the set $|D \to D|$ into $|D|$. The next result shows that this function, or operator on functions, is in fact approximable.

**THEOREM 4.2.** For any domain $D$, there is an approximable mapping

$$
\mathrm{fix} : (D \to D) \to D
$$

such that if $f : D \to D$ is any approximable mapping, then

(i) $\mathrm{fix}(f) = f(\mathrm{fix}(f)).$

Furthermore, if $x \in |D|$, then

(ii) $f(x) \subseteq x$ implies $\mathrm{fix}(f) \subseteq x.$

And this last property implies that $\mathrm{fix}$ is unique. Explicitly we can characterize $\mathrm{fix}$ by the equation:

(iii)

$$
\mathrm{fix}(f) = \bigcup_{n=0}^{\infty} f^n(\bot),
$$

for all $f : D \to D.$
**Proof:** Formula (iii) can be put in a more elementary form:

$$
\mathrm{fix}(f) = \{ X \mid \Delta f^n X,\ \text{for some } n \in \mathbf{N} \}.
$$

To show an elementwise mapping approximable we can use the formula of Exercise 2.9, applied to the above as the definition of $\mathrm{fix}$:

$$
(*)\quad \mathrm{fix}(f) = \bigcup \{ \mathrm{fix}(\uparrow F) \mid f \in [F] \},
$$

where $F$ ranges over the neighbourhoods of $(D \to D)$, and where $\uparrow F$ can be considered to be the least element of $F$ as calculated in 3.9.

Now from the definition of $\mathrm{fix}$, it is clear that whenever $f \subseteq g$, then $\mathrm{fix}(f) \subseteq \mathrm{fix}(g)$, because $f^n \subseteq g^n$. (That is, $\mathrm{fix}$ is obviously monotone.) Next, if $f \in F$, then $\uparrow F$ is a (finite) approximation to $f$; so $\uparrow F \subseteq f$ and $\mathrm{fix}(\uparrow F) \subseteq \mathrm{fix}(f)$. This means that half of equation (*) already holds by monotonicity. All that is left is to prove the other half.

So suppose $X \in \mathrm{fix}(f)$. Then, as we have already remarked, there is a finite sequence of neighbourhoods where

$$
\Delta = X_0\ f\ X_1\ \dots\ X_{n-1}\ f\ X_n = X.
$$

Let the function-space neighbourhood be defined as

$$
F = \bigcap \{ [X_i, X_{i+1}] \mid i < n \},
$$

and note that since $f \in [F]$ we have at once consistency. But, by 3.9, $\uparrow F \in [F]$, so the *same* sequence of $X_i$ is sufficient to show that

$$
X \in \mathrm{fix}(\uparrow F).
$$

In other words, if $X$ belongs to the left-hand side of (*), it also belongs to the right-hand side. This completes the proof of (*).

Formula (i) is just a restatement of what we proved in 4.1. And (ii) follows easily, because $f(x) \subseteq x$ implies that $\Delta \in x$ and whenever $X \in x$ and $X\ f\ Y$, then $Y \in x$. Thus, by induction, if $\Delta f^n X$, then $X \in x$. So $\mathrm{fix}(f) \subseteq x$.

Finally, if $\mathrm{fax} : (D \to D) \to D$ were any other operator satisfying (i) and (ii), we would prove at once that

$$
\mathrm{fix}(f) \subseteq \mathrm{fax}(f) \quad \text{and}
$$

$$
\mathrm{fax}(f) \subseteq \mathrm{fix}(f).
$$

That is to say, the two operators are identical. $\square$
