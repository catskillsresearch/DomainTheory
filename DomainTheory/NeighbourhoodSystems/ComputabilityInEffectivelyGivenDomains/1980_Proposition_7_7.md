# Proposition 7.7

## Human-English

**PROPOSITION 7.7.** For any effectively given domain $D$, the domain $D^\S$ is also effectively given, and all the combinators of Example 6.1 prove to be computable.

*Proof:* This proof is essentially an exercise, but it is useful to have an easy-to-grasp example. Indeed, to make things easy to reason about, we can assume that $D$ is a system over $\Delta = \mathbf{N}$, and that in the presentation where

$$D = \{ X_n \mid n \in \mathbf{N} \},$$

the relation $k \in X_n$ is *recursive* in $k$ and $n$. (It is worth thinking why this is so.) Of course, a lot of other things are recursive also.

<!-- page 125 -->

Now what kind of a system is $D^\S$? The construction of 6.1 made it a system over a certain set of strings $\Gamma$. For the sake of checking various assertions about computability, we are transposing everything back to $\mathbf{N}$. (These are all denumerable sets in any case.) The set $\Gamma$ is divided into three equally big parts, and we can do the same for $\mathbf{N}$. Let us write for any $m, k \in \mathbf{N}$ and subset $X \subseteq \mathbf{N}$:

$$mX + k = \{ m \cdot n + k \mid n \in X \}.$$

Then by splitting the integers modulo 3 we have:

$$\mathbf{N} = 3\mathbf{N} \cup (3\mathbf{N} + 1) \cup (3\mathbf{N} + 2),$$

and this equation is quite analogous to that for $\Gamma$. We then propose this definition for $D^\S$:

$$D^\S = \{\mathbf{N}\} \cup \{3X \mid X \in D\} \cup \{(3X + 1) \cup (3Y + 2) \mid X, Y \in D^\S\},$$

but this does not make the enumeration of $D^\S$ all that obvious. This is one way to do it:

$$V_0 = \mathbf{N} \ ; \ V_{2n+1} = 3X_n \ ; \ V_{2n+2} = (3V_{p(n)} + 1) \cup (3V_{q(n)} + 2).$$

Here $p$ and $q$ are the inverse of the pairing functions mentioned in 7.4. They must be chosen so that $p(n) < n$ and $q(n) < n$ for all $n \in \mathbf{N}$. Thus, in calculating $V_k$ where $k = 2n + 2$ we will be using $V_{p(n)}$ and $V_{q(n)}$ where both subscripts are strictly less than $k$. This observation is required so that $m \in V_k$ is going to be a recursive relation. What we claim is that

$$D^\S = \{V_k \mid k \in \mathbf{N}\}.$$

It should be clear that everything on the right belongs to $D^\S$. What needs an inductive argument is that everything in $D^\S$ is eventually of the form $V_k$. But this should be fairly obvious owing to the properties of $r : \mathbf{N} \times \mathbf{N} \leftrightarrow \mathbf{N}$.

The reader also has to check that 7.1(i)–(ii) hold for the $V_k$. The idea is that any such check is either (1) trivial, or (2) something already assumed about $D$ and the $X_n$, or (3) can be thrown back to some sets $V_m$ with strictly smaller subscripts. Therefore, the checks will give an answer in finite time according to an effective reduction.

Next for the combinators, we have to translate neighbourhood relations into relations among integer indices. A selection of examples must suffice,

$$X_n\ (\lambda x.\, x^\S)\ V_k \text{ iff } V_{2n+1} \subseteq V_k$$

<!-- page 126 -->

$$V_m \ \mathrm{proj}_0 \ V_k \text{ iff } k = 0 \text{ or } \exists n \in \mathbf{N}.\, m = 2n + 2 \text{ and } V_{p(n)} \subseteq V_k.$$

The reader should write out other cases. $\square$

## AI: Human-English to AI-Lean

**[Proposition_7_7.lean](Proposition_7_7.lean)**

@import "Proposition_7_7.lean"
