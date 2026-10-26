# Theorem 4.1

**THEOREM 4.1.** For any approximable mapping $f : D \to D$ on any domain, there exists a least element $x \in |D|$ where

$$
f(x) = x.
$$

**Proof:** Let $f^n$ for $n \in \mathbf{N}$ stand for the $n$-fold composition of $f$ with itself. That is,

$$
f^0 = I_D, \text{ and}
$$

$$
f^{n+1} = f \circ f^n.
$$

Define

$$
x = \{ X \in D \mid \Delta\ f^n\ X, \text{ for some } n \in \mathbf{N} \}.
$$

We see $X \in x$ iff there is a finite sequence $\Delta = X_0, X_1, \ldots, X_n = X$ where $X_i\ f\ X_{i+1}$ holds for all $i < n$. Now since $\Delta\ f\ \Delta$ automatically holds, a sequence for an $X \in x$ can always be extended to a longer sequence just by adding more $\Delta$'s on the front.

We want to prove $x \in |D|$. Clearly $\Delta \in x$; and if $X \subseteq Y$ and $X \in x$, then $Y \in x$. All that remains to be shown is the closure of $x$ under intersection. Note that if

$$
U\ f\ V \quad \text{and} \quad U'\ f\ V'
$$

hold and $U, U'$ are consistent in $D$, then $V$ and $V'$ are consistent and

<!-- page 56 -->

$(U \cap U')\ f\ (V \cap V')$

must hold. Generalizing this to sequences, if

$$
\Delta = X_0\ f\ X_1\ f\ \cdots\ f\ X_n = X, \text{ and}
$$

$$
\Delta = Y_0\ f\ Y_1\ f\ \cdots\ f\ Y_n = Y
$$

both hold (and note we have arranged the lengths of the two sequences to be equal), then each pair $X_i, Y_i$ is consistent and we have

$$
\Delta = (X_0 \cap Y_0)\ f\ (X_1 \cap Y_1)\ f\ \cdots\ f\ (X_n \cap Y_n) = X \cap Y.
$$

This establishes the desired closure.

We also note that if $X \in x$ and $X\ f\ Y$ then $Y \in x$. Therefore, $f(x) \subseteq x$ and indeed by its very construction $x$ is the *least* element of $|D|$ with this property. (Why?) But $f$ is monotone, so $f(f(x)) \subseteq f(x)$; hence, $x = f(x)$. By what we have already said it must be the least such element. $\square$

Because the element we have shown to exist in 4.1 is a least element, it is unique. That is, we have associated with each $f : D \to D$ a special element $x_f \in |D|$ determined by the choice of $f$. A function has therefore been defined mapping the set $|D \to D|$ into $|D|$. The next result shows that this function, or operator on functions, is in fact approximable.

**[Theorem_4_1.lean](Theorem_4_1.lean)**

@import "Theorem_4_1.lean"
