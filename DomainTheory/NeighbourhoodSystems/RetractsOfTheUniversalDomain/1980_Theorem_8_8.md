# Theorem 8.8

## Human-English

**THEOREM 8.8.** The system $\mathcal{U}$ is universal in the sense that, for every countable neighbourhood system $\mathcal{D}$, we have
$$\mathcal{D} \trianglelefteq \mathcal{U}.$$
Moreover, if $\mathcal{D}$ is effectively given, then the projection pair making the embedding can be taken as computable. Indeed there is a correspondence between effectively presented domains and the computable, finitary projections of $\mathcal{U}$.

*Proof:* As $\mathcal{D}$ is countable, we can assume that
$$\mathcal{D} = \{X_n \mid n \in \mathbb{N}\},$$

<!-- page 141 -->

where $\mathcal{D}$ is a system over a set $\Delta$ (say, $X_0 = \Delta$). We shall do the effective and general cases together, where for the latter all remarks on recursiveness are just left out. So, if we want $\mathcal{D}$ effectively given, the above enumeration should be taken as the computable presentation.

Without loss of generality we can assume $\mathcal{D} \cong \mathcal{D}^\dagger$, since otherwise we would just replace $\mathcal{D}$ by $\mathcal{D}^\dagger$. The advantage of this preparation is that unions in $\mathcal{D}^\dagger$ keep things rather *separate* (as we noticed in constructing $\mathbb{P}\mathcal{D}$). In particular, we can be sure of this equivalence:

$$(\blacklozenge) \qquad X_m \subseteq \bigcup_{i < k} X_{n_i} \quad \text{iff} \quad \exists i < k.\ X_m \subseteq X_{n_i}.$$

This property, for example, fails for the system $\mathcal{U}$ as presented in Definition 8.7. However, that observation is of no moment, because we are employing the assumption with respect to $\mathcal{D}$ not $\mathcal{U}$.

The reason for the assumption is this: for $\delta \in \{+, -\}$ define for $X \in \mathcal{D}$:

$$
\begin{aligned}
\delta X &= X && \text{if } \delta = + ; \\
&= \Delta \setminus X && \text{if } \delta = - .
\end{aligned}
$$

(A similar notation will be used for $Y \in \mathcal{U}$.) Then for $\delta \in \{+, -\}^n$ the sets of the form

$$\bigcap_{i < n} \delta_i X_i \quad (= X_\delta, \text{ for short})$$

form a partition of $\Delta$ into (at most) $2^n$ parts. The reason for assumption $(\blacklozenge)$ is that we can effectively decide for each $\delta \in \{+, -\}^n$ whether one of these intersections is empty or not. (Why? — assuming that $\mathcal{D}$ is effectively given, of course). If for some reason we had not wanted to pass to $\mathcal{D}^\dagger$, we could have made this stronger assumption of decidability on the (positive) system $\mathcal{D}$. ($\mathcal{U}$, for example, satisfies it.)

Suppose, corresponding to $X_0, X_1, \ldots, X_{n-1}$, we have selected $Y_0, Y_1, \ldots, Y_{n-1} \in \mathcal{U}$ so that, for all $\delta \in \{+, -\}^n$,

$$(\blacksquare) \qquad \bigcap_{i < n} \delta_i X_i = \emptyset \quad \text{iff} \quad \bigcap_{i < n} \delta_i Y_i = \emptyset.$$

<!-- page 142 -->

We wish to show - effectively - how to choose $Y_n$ corresponding to $X_n$, so that $(\blacksquare)$ holds with $n+1$ replacing $n$. Proceeding inductively, we obtain a recursive enumeration of sets $Y_n \in \mathcal{U}$ so that

$$\mathcal{D} \equiv \{ Y_n \mid n \in \mathbb{N} \} \triangleleft \mathcal{U} .$$

Clearly the isomorphism (matching $X_i$ to $Y_i$) will be computable and the projection is computable. (It will then remain only to consider the arbitrary finitary computable projection to complete the proof of the theorem.)

So, consider $X_n$; for each $\delta \in \{+, -\}^n$ there are four cases:

$$
\begin{aligned}
X_\delta \cap X_n &= \emptyset, & X_\delta \cap -X_n &= \emptyset, \\
X_\delta \cap X_n &\neq \emptyset, & X_\delta \cap -X_n &\neq \emptyset .
\end{aligned}
$$

Corresponding to $X_\delta$ is a similar intersection $Y_\delta$. If $X_\delta$ were $\emptyset$, then $Y_\delta$ would be also. If not, $Y_\delta \subseteq [0, 1)$ is a union of rational intervals that can be written down explicitly. (Why?) In our four cases on $X_n$, the first implies the fourth. (Why?) Thus, we need only make some choices in these circumstances:

$$
\begin{aligned}
X_\delta \cap X_n = \emptyset &: \text{choose } I_{\delta, n} = \emptyset ; \\
X_\delta \cap -X_n = \emptyset &: \text{choose } I_{\delta, n} = Y_\delta ; \\
\text{otherwise} &: \text{choose } I_{\delta, n} \subseteq Y_\delta, \text{ with } \emptyset \neq I_{\delta, n} \neq Y_\delta .
\end{aligned}
$$

All these cases are decidable by assumption on $\mathcal{D}$, and the effective choice of (unions of) intervals is effective by construction of $\mathcal{U}$. Now set

$$Y_n = \bigcup_{\delta \in \{+, -\}^n} I_{\delta, n} \neq \emptyset .$$

The set $Y_n \in \mathcal{U}$, it can be found effectively, and $(\blacksquare)$ is obviously satisfied for $n+1$ .

Finally, suppose that $a$ is a computable, finitary projection of $\mathcal{U}$. As we have seen in the proof of 8.5, the domain corresponding to the range of $a$ is isomorphic to the neighbourhood system

$$\{ Y \in \mathcal{U} \mid Y \ a \ Y \} \triangleleft \mathcal{U} .$$

<!-- page 143 -->

Clearly, if $a$ as a set of ordered pairs of neighbourhoods is recursively enumerable, then the above set is also recursively enumerable (because equality between neighbourhoods is decidable). It follows easily that the subsystem is effectively given as a neighbourhood system in its own right. $\square$

We have now proved that $\mathcal{U}$ is a nice and big domain that is nicely behaved with respect to computable mappings. It has some very interesting subdomains; to name a few:

$$\mathcal{U} + \mathcal{U}, \quad \mathcal{U} \oplus \mathcal{U}, \quad \mathcal{U} \times \mathcal{U}, \quad \mathcal{U} \otimes \mathcal{U}$$

$$\mathcal{U}_\bot, \quad \mathcal{U}^\infty, \quad \mathcal{U}^\S, \quad \mathbb{P}\mathcal{U}, \quad \mathcal{U} \to \mathcal{U}$$

That all of these are $\trianglelefteq \mathcal{U}$ follows from knowing that they are all effectively presented. What we wish to check next is that they all combine well with respect to projections. To this end the explicit definitions are given for the constructs $+$, $\times$, and $\to$, and the details of the others are left for the exercises.

## AI: Human-English to AI-Lean

**[Theorem_8_8.lean](Theorem_8_8.lean)**

@import "Theorem_8_8.lean"
