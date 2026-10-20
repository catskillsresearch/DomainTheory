# Retracts of the universal domain

In order to be able to have a fully flexible method of solving domain equations and to be able to see why the domains obtained are effectively given, we shall embed all the desired domains in one "largest" domain. This universal domain will be easily shown to be effectively given, and the mappings needed to extract the other domains will be found to be computable. In order to be able to carry out this programme, we investigate first how certain subdomains correspond to mappings — the so-called *retracts*. An advantage of this analysis is that all the necessary definitions can be written out in $\lambda$-calculus notation, thus demonstrating the power of our mathematical programming language.

**DEFINITION 8.1.** A retraction of a given domain $E$ is an approximable mapping $a : E \to E$ such that $a \circ a = a$. $\square$

**PROPOSITION 8.2.** If $D \triangleleft E$ and if $a : E \to E$ is defined by

$$X \ a \ Z \quad \text{iff} \quad \exists Y \in D.\ X \subseteq Y \subseteq Z$$

for all $X, Z \in E$, then $a$ is a retraction and $|D|$ is isomorphic to the fixed-point set of $a$, the set $\{y \in |E| \mid a(y) = y\}$, under inclusion.

*Proof:* That $a$ is an approximable mapping is a direct consequence of Definition 6.10. Indeed, in the notation of Proposition 6.12, we have

$$a = i \circ j,$$

and this is another proof that $a$ is approximable. This remark is also convenient, since we know from 6.10

$$j \circ i = I_D.$$

Therefore, we find:

$$a \circ a = i \circ j \circ i \circ j = i \circ j = a;$$

and so $a$ is a retraction.

We can also employ $i$ and $j$ to give the isomorphism on $|D|$. If $x \in |D|$, then $i(x) \in |E|$ and we calculate:
$$a(i(x)) = i \circ j \circ i(x) = i(x).$$

Thus, $i(x)$ belongs to the fixed-point set of $a$. In the other direction, if $a(y) = y$, then $i(j(y)) = y$. But $j(y) \in |D|$, so $i$ maps $|D|$ one-one and onto the fixed-point set of $a$. As $i$ and $j$ are monotone, the map is an isomorphism with respect to $\sqsubseteq$. $\square$

Not every retraction comes from a relationship like $D \triangleleft E$; in fact, we can see from the definition of $a$ above that $a \sqsubseteq 1_E$. But, as is indicated in Exercise 8.11, even this condition is not sufficient to characterize the kind of retractions provided by 8.2. The characterization is as follows.

**DEFINITION 8.3.** A retraction $a : E \to E$ is called a *projection* provided

$$a \sqsubseteq 1_E;$$

it is *finitary* iff its fixed-point set is isomorphic to a domain. $\square$

**EXAMPLES 8.4.** If a system $D$ over $\Delta$ is not trivial, then the two element system $O = \{\{0\}, \{0,1\}\}$ comes from a retraction on $D$. Specifically, define a combinator

$$\mathrm{check} : D \to O$$

by the relation

$$X \ \mathrm{check}\ Y \quad \text{iff either } Y = \{0,1\} \text{ or } X \neq \Delta.$$

We see $\mathrm{check}(x) = \bot_O$ iff $x = \bot_D$. We leave to the reader the definition of a combinator:

$$\mathrm{fade} : O \times D \to D,$$

where we have for $t \in |O|$ and $x \in |D|$:

$$\begin{aligned}
\mathrm{fade}(t,x) &= \bot_D, \text{ if } t = \bot_O; \\
&= x, \text{ if not.}
\end{aligned}$$

Now, take any $u \in |D|$ with $u \neq \bot$, and define

$$a(x) = \mathrm{fade}(\mathrm{check}(x), u).$$

Then $a$ is a retraction (not a projection in general) and the range of $a$ is isomorphic to $O$.
Another way of using these combinators is to find $(D \to_{\perp} E)$ as a retraction of $(D \to E)$. Specifically, define a combinator

$$\mathrm{strict} : (D \to E) \to (D \to E)$$

by the equation

$$\mathrm{strict}(f) = \lambda x.\ \mathrm{fade}(\mathrm{check}(x), f(x)),$$

where this time

$$\mathrm{fade} : O \times E \to E\ .$$

The range of $\mathrm{strict}$ consists exactly of the strict functions and this time $\mathrm{strict}$ is a projection whose range is indeed a domain.

Similarly, we can find a projection on $D \times E$ with a range isomorphic to $D \otimes E$ by the combinator such that:

$$\mathrm{smash}(x, y) = \mathrm{fade}(\mathrm{check}(x), \mathrm{fade}(\mathrm{check}(y), \langle x, y \rangle)),$$

for $x \in |D|$ and $y \in |E|$. $\square$

**THEOREM 8.5.** For an approximable mapping $a : E \to E$ the following are equivalent:

(i) $a$ is a finitary projection;

(ii) $a(x) = \{Y \in E \mid \exists X \in x.\, X \subseteq Y \land X \ a \ X\}$, for all $x \in |E|$.

*Proof:* Suppose $a$ satisfies (ii) first. Inasmuch as $X \in x$ and $X \subseteq Y$ always imply $Y \in x$, for all $x \in |E|$, we see $a(x) \subseteq x$ must always hold. Moreover, it is obvious that $X \in x$ and $X \ a \ X$ always imply $X \in a(x)$; therefore, $a(x) \subseteq a(a(x))$ for all $x \in |E|$. This shows that $a$
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

**THEOREM 8.6.** For any domain $E$ define

$$\mathrm{sub} : (E \to E) \to (E \to E)$$

by the formula

$$X \ \mathrm{sub} \ (f) \ Z \quad \text{iff} \quad \exists Y \in E.\quad X \subseteq Y \ \ f \ Y \subseteq Z,$$
for all $X, Z \in E$ and all $f : E \to E$. Then the range of $\mathrm{sub}$ consists exactly of the finitary projections on $E$, and moreover $\mathrm{sub}$ itself is a finitary projection on $(E \to E)$. If $E$ is effectively given, then $\mathrm{sub}$ is computable.

*Proof:* It is trivial to check that $\mathrm{sub}(f)$ is always approximable. Also, it is obvious from the definition that the correspondence

$$f \mapsto \mathrm{sub}(f)$$

preserves directed unions of $f$'s. Thus, $\mathrm{sub}$ is itself approximable. We note that

$$X \subseteq Y \ \ f \ Y \subseteq Z \text{ always implies } X \ f \ Z;$$

hence, $\mathrm{sub}(f) \subseteq f$ holds. Also

$$Y \ f \ Y \text{ always implies } Y \ \mathrm{sub}(f) \ Y,$$

hence, $\mathrm{sub}(f) \subseteq \mathrm{sub}(\mathrm{sub}(f))$ holds. This shows $\mathrm{sub}$ to be a projection on $(E \to E)$. The effectiveness of the definition makes it also clear that $\mathrm{sub}$ is computable when $E$ has a computable presentation.

Since, $\mathrm{sub}$ is a projection, its range is the same as its fixed-point set. If

$$\mathrm{sub}(a) = a,$$

then there is no problem in checking that $a$ satisfies 8.5(ii) *and conversely*. So the range of $\mathrm{sub}$ picks out exactly the finitary projections in view of 8.5.

Finally, to prove that $\mathrm{sub}$ is a finitary projection of $(E \to E)$, we invoke 6.11 and remark that, in view of 8.2, the fixed point set (range) of $\mathrm{sub}$ is in a one-one inclusion-preserving correspondence with the domain $\{D \mid D \triangleleft E\}$. $\square$

These results have almost completely translated the theory of $\triangleleft$-subdomains into $\lambda$-calculus via the sub-combinator. One last step will complete the passage, and then we shall be able to return to solving domain equations.
**DEFINITION 8.7.** Let $\mathbb{Q}$ be the set of rational numbers, and let
$$[0, 1) = \{q \in \mathbb{Q} \mid 0 \le q < 1\},$$
and similarly for $[r, s)$ for any $r < s$ in $\mathbb{Q}$. The neighbourhood system $\mathcal{U}$ over $[0, 1)$ is the set of all non-empty finite unions of rational intervals $[r, s)$ with $0 \le r < s \le 1$. $\square$

A picture of a typical element of $\mathcal{U}$ could be drawn like this:

```
0    r_0  r_1     r_2  r_3     r_4  r_5     1
[======)       [=====)       [=====)
```

Note that any union can be taken as a *disjoint* union of the form
$$\bigcup_{i \le n} [r_{2i}, r_{2i+1})$$
where $0 \le r_0 < r_1 < r_2 < \cdots < r_{2n} < r_{2n+1} \le 1$. (Hint: Any overlapping intervals or abutting intervals can always be combined into one long interval.) It is a most elementary exercise to show that, by virtue of this representation, the system $\mathcal{U}$ has a computable presentation. (Some isomorphic versions of $\mathcal{U}$ — equally effective — are recorded in the exercises.) Note that $\mathcal{U}$ has no minimal neighbourhoods: every set in $\mathcal{U}$ can be written as the union of two disjoint sets in $\mathcal{U}$. (Hint: Use the density of the ordering of $\mathbb{Q}$.) The significance of $\mathcal{U}$ can now be explained.

**THEOREM 8.8.** The system $\mathcal{U}$ is universal in the sense that, for every countable neighbourhood system $\mathcal{D}$, we have
$$\mathcal{D} \trianglelefteq \mathcal{U}.$$
Moreover, if $\mathcal{D}$ is effectively given, then the projection pair making the embedding can be taken as computable. Indeed there is a correspondence between effectively presented domains and the computable, finitary projections of $\mathcal{U}$.

*Proof:* As $\mathcal{D}$ is countable, we can assume that
$$\mathcal{D} = \{X_n \mid n \in \mathbb{N}\},$$
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
Clearly, if $a$ as a set of ordered pairs of neighbourhoods is recursively enumerable, then the above set is also recursively enumerable (because equality between neighbourhoods is decidable). It follows easily that the subsystem is effectively given as a neighbourhood system in its own right. $\square$

We have now proved that $\mathcal{U}$ is a nice and big domain that is nicely behaved with respect to computable mappings. It has some very interesting subdomains; to name a few:

$$\mathcal{U} + \mathcal{U}, \quad \mathcal{U} \oplus \mathcal{U}, \quad \mathcal{U} \times \mathcal{U}, \quad \mathcal{U} \otimes \mathcal{U}$$

$$\mathcal{U}_\bot, \quad \mathcal{U}^\infty, \quad \mathcal{U}^\S, \quad \mathbb{P}\mathcal{U}, \quad \mathcal{U} \to \mathcal{U}$$

That all of these are $\trianglelefteq \mathcal{U}$ follows from knowing that they are all effectively presented. What we wish to check next is that they all combine well with respect to projections. To this end the explicit definitions are given for the constructs $+$, $\times$, and $\to$, and the details of the others are left for the exercises.

**DEFINITION 8.9.** Let the computable projection pairs $i_+ : \mathcal{U} + \mathcal{U} \to \mathcal{U}$ and $j_+ : \mathcal{U} \to \mathcal{U} + \mathcal{U}$ be fixed. Similarly choose $i_\times, j_\times$ and $i_\to, j_\to$ for $\mathcal{U} \times \mathcal{U}$ and $\mathcal{U} \to \mathcal{U}$. Define:

$$a + b = \mathrm{cond} \circ \langle \mathrm{which}, i_+ \circ \mathrm{in}_0 \circ a \circ \mathrm{out}_0, i_+ \circ \mathrm{in}_1 \circ b \circ \mathrm{out}_1 \rangle \circ j_+ \ ;$$

$$a \times b = i_\times \circ \langle a \circ \mathrm{proj}_0, b \circ \mathrm{proj}_1 \rangle \circ j_\times \ ;$$

$$a \to b = i_\to \circ (\lambda f.\ b \circ f \circ a) \circ j_\to \ ,$$

for all $a, b : \mathcal{U} \to \mathcal{U}$. $\square$

These interesting(computable!) combinators on elements of $\mathcal{U} \to \mathcal{U}$ have many, many properties. We shall, however, only see what they do to projections.

**PROPOSITION 8.10.** If $a, b : \mathcal{U} \to \mathcal{U}$ are projections, then so are $a + b$, $a \times b$, and $a \to b$. If $a$ and $b$ are finitary, then so are the others; for the fixed-point set of each of them is isomorphic to the corresponding construct applied to the domains determined by $a$ and $b$.
*Proof:* Suppose that $a, b \sqsubseteq I_{\mathcal{U}}$ (= $I$ for short). Then

$$a + b \sqsubseteq I + I = i_+ \circ j_+ \sqsubseteq I.$$

The other cases are similar.

Suppose $a = a \circ a$ and $b = b \circ b$, then, for example,

$$
\begin{aligned}
(a \times b) \circ (a \times b) &= i_\times \circ \langle a \circ \mathrm{proj}_0,\ b \circ \mathrm{proj}_1 \rangle \circ \langle a \circ \mathrm{proj}_0,\ b \circ \mathrm{proj}_1 \rangle \circ j_\times \\
&= i_\times \circ \langle a \circ a \circ \mathrm{proj}_0,\ b \circ b \circ \mathrm{proj}_1 \rangle \circ j_\times \\
&= a \times b.
\end{aligned}
$$

The other cases are similar.

Now in case the fixed-point sets of $a$ and $b$ are domains, they are respectively isomorphic to

$$D_a = \{ X \in \mathcal{U} \mid X \ a \ X \} \quad \text{and}$$
$$D_b = \{ Y \in \mathcal{U} \mid Y \ b \ Y \}.$$

We have to show, for example, that

$$D_a \to D_b \cong D_{a \to b}.$$

Now to simplify matters, remark that the fixed-point set of $a \to b$ on $\mathcal{U}$ is isomorphic to the fixed-point set of $\lambda f.\ b \circ f \circ a$ on $(\mathcal{U} \to \mathcal{U})$. (Hint: use $i_\to$ and $j_\to$ to set up the isomorphism.) So we have to think what it is for an $f : \mathcal{U} \to \mathcal{U}$ to satisfy

$$f = b \circ f \circ a.$$

Notice that we might as well say that $a : \mathcal{U} \to D_a$ and that this map is the other half of an obvious projection pair where

$$i_a : D_a \to \mathcal{U},$$

and $i_a \circ a = a$ and $a \circ i_a = i_a$. So if $g : D_a \to D_b$, let

$$f = i_b \circ g \circ a;$$

then $b \circ f \circ a = f$. Conversely, if $f$ is like this, then let

$$g = b \circ f \circ i_a.$$

Thus, $i_b \circ g \circ a = b \circ f \circ a = f$; so there is an order-preserving isomorphism between the $g : D_a \to D_b$ and the $f = b \circ f \circ a$.
The isomorphism proofs for $+$ and $\times$ are similar. $\square$

Well, this was a lot of work, but the pay-off is rather handsome. What we have done is transpose all the

$$D_a \triangleleft U$$

over to finitary projections $a : U \to U$. This transposition is an isomorphism, because

$$D_a \triangleleft D_b \text{ iff } a \sqsubseteq b.$$

Moreover, by the method of 8.9 and 8.10, all our favourite constructs have been made into *combinators*, that is, approximable — even computable — maps on the domain of finitary projections. *ALL APPROXIMABLE (COMPUTABLE) MAPS HAVE (COMPUTABLE) FIXED POINTS.* And there you are! The standard fixed-point method is available to obtain computable (i.e. effectively given) solutions to *all* domain equations (even sets of equations) where the constructs can be reworked in *this* way to be defined on projections. Examples are suggested in the exercises.

Another pay-off concerns the $\lambda$-calculus itself. Inasmuch as

$$U + U, \quad U \times U, \quad U \to U \triangleleft U,$$

we might just as well forget the outside world and regard all these useful domains as being part of $U$. For example, on the left we have the new notation and on the right the old notation:

$$
\begin{aligned}
\mathrm{which}(z) &= \mathrm{which}(j_+(z)) ; \\
\mathrm{in}_i(x) &= i_+(\mathrm{in}_i(x)), \quad i = 0, 1 ; \\
\mathrm{out}_i(x) &= \mathrm{out}_i(j_+(x)), \quad i = 0, 1 ; \\
\langle x, y \rangle &= i_\times(\langle x, y \rangle) ; \\
\mathrm{proj}_i(z) &= \mathrm{proj}_i(j_\times(z)), \quad i = 0, 1 ; \\
u(x) &= j_\to(u)(x) ; \\
\lambda x.\,\tau &\cong i_\to(\lambda x.\,\tau) .
\end{aligned}
$$

And, there is no reason to stop here. The system

$$T \cong \{\{0, 1/2\}, \{1/2, 1\}, \{0, 1\}\} \triangleleft U,$$

so we might as well think of
$$\text{true, false} \in |U|$$

and think of $\mathrm{cond} : U \times U \times U \to U$. No! that is wrong: under the new regime *EVERYTHING IS AN ELEMENT OF U*. With the new meaning of $\lambda$, all functions, all pairs, all combinators, all constructs become elements of $U$.

It takes a little time to get used to "universal conscription" with all elements doing (at least) double duty in the same domain, but there are many advantages, both notational and conceptual.

**EXERCISES**

**EXERCISE 8.11.** Let $\mathbb{Q}$ be the set of rational numbers and define a neighbourhood system by the equation

$$R = \{[0, r) \mid r \in \mathbb{Q} \text{ and } 0 < r \le 1\}.$$

Show that the following defines an approximable map $a : R \to R$:

$$[0, r) \ a \ [0, s) \quad \text{iff} \quad r < s \text{ or } r = s = 1.$$

Show in addition that $a$ is a projection where the fixed-point set of $a$ is in a one-one correspondence with the *real* numbers between 0 and 1 inclusive. (Hint: Recall Dedekind cuts and show $\subseteq$ matches $\le$.) Conclude that $a$ is *NOT* finitary. (Hint: Aside from $\bot$ there are no finite elements for $\{x \mid x = a(x)\}$.)

**EXERCISE 8.12.** Generalize the notation $2X + 1$ for subsets $X \subseteq \mathbb{N}$ to sets of the form

$$2^k X + \ell, \quad \text{where } \ell < 2^k.$$

Let $V$ be the non-empty finite unions of sets $2^k \mathbb{N} + \ell$. Show that $U \cong V$ and that the isomorphism is effective, thus obtaining another presentation of $U$.

**EXERCISE 8.13.** (For logicians.) Prove that the universal domain $U$ is isomorphic to the domain of all proper filters of the free Boolean algebra on $\aleph_0$-generators (= the Lindenbaum algebra of propositional calculus). (For topologists.) Connect this
representation of $\mathcal{U}$ with the collection of non-empty open subsets of the product space $2^{\mathbf{N}}$ (= Cantor space).

**EXERCISE 8.14.** A retraction $a : D \to D$ is called a *closure operator* iff $I_D \sqsubseteq a$. On a domain like $P\mathbf{N}$, give some examples of closure operators. (Hint: Close up a set of integers under addition. Is this continuous on $P\mathbf{N}$?) Prove in general for any closure $a : D \to D$ that the fixed-point set of $a$ is always a finitary domain. (Hint: Show that the fixed-point set is closed under intersections and directed unions.) What are the finite elements of the fixed-point set?

**EXERCISE 8.15.** Give a direct proof that the domain $\{X \mid X \triangleleft D\}$ is effectively presented if $D$ is. (Hint: The finite elements of the domain correspond exactly to the finite systems $X \triangleleft D$.) In the case of $D = \mathcal{U}$, show that the computable elements of the domain correspond exactly to the effectively presented domains (up to effective isomorphism).

**EXERCISE 8.16.** For finitary projections $a : E \to E$, write

$$D_a = \{X \in E \mid X \sqsubseteq a X\}$$

(cf. 8.5.). Show that for any two such projections $a, b : E \to E$ we have

$$a \sqsubseteq b \quad \text{iff} \quad D_a \triangleleft D_b.$$

(This fills in the gap at the end of the proof of 8.6.) Also finish off the proof of 8.8 by showing that if $E$ is effectively given and $a : E \to E$ is computable, then $D_a$ is effectively given.

**EXERCISE 8.17.** Find explicitly (if possible) the projection pairs for $\mathcal{U} + \mathcal{U}$, $\mathcal{U} \times \mathcal{U}$, and $\mathcal{U} \to \mathcal{U}$ needed for 8.9. Are any of these domains isomorphic with $\mathcal{U}$? (The author does not know a really good construction for $\mathcal{U} \to \mathcal{U}$.) Find a universal domain $V \neq \mathcal{U}$.
**EXERCISE 8.18.** Many of the cases of 8.10 were left unproved. Please establish these assertions explicitly.

**EXERCISE 8.19.** Suppose we know both

$$T \quad \text{and} \quad E \to E \trianglelefteq E \ .$$

Does it follow that $E + E$ and $E \times E \trianglelefteq E$?

**EXERCISE 8.20.** For any system we know $D \trianglelefteq D + D$, but what about

$$D \trianglelefteq D \times D \quad \text{and} \quad D \trianglelefteq D \to D \ ?$$

Would these projections be computable if $D$ is effectively given? Are there more than one projection pair in each case?

**EXERCISE 8.21.** Using the fixed-point construction, show that there is a continuous and computable operator $\lambda a.\, a^{\S}$, such that if $a$ is a finitary projection of $U$, then

$$D_{a^{\S}} \cong (D_a)^{\S} \ .$$

**EXERCISE 8.22.** Which of the two relations hold:

$$B \trianglelefteq C \quad \text{or} \quad C \trianglelefteq B \ ?$$

Or do they both hold? In general if we use domain equations

$$D = T(D) + S(D) \ , \quad \text{and}$$

$$E = T(E) \ ,$$

will $E \trianglelefteq D$ hold? What projections do you see in the examples in 6.2?

**EXERCISE 8.23.** Suppose a construct $T$ on domains can be made into a computable operator $t : (U \to U) \to (U \to U)$ so that whenever $a : U \to U$ is a finitary projection, then so is $t(a)$ and

$$D_{t(a)} \cong T(D_a) \ .$$

Does it follow that $\|t\| = \mathrm{fix}(t)$ is such that

$$D_{\|t\|} \cong T(D_{\|t\|})$$
really is the initial solution of the domain equation with respect to projections? Since $t$ is computable, will this solution be effectively given?

**EXERCISE 8.24.** Suppose $S$ and $T$ are two (binary-argument) constructs on domains that can be made into computable operators on projections of the universal domain. Show that we can therefore find a pair of effectively presented domains such that
$$
D \cong S(D, E) \quad \text{and} \quad E \cong T(D, E).
$$

**EXERCISE 8.25.** The problem is to find non-trivial solutions to the domain equation
$$
(\spadesuit) \qquad D \cong D \to D.
$$
Show that the "obvious" solution by retracts is of no use because
$$
1 \to 1 = 1
$$
for projections. Change the method as follows. Show first
$$
U^\infty \times U^\infty \cong U^\infty.
$$
Next solve
$$
D \cong D \to U^\infty
$$
and remark that $U \triangleleft D$; so $D$ is universal and non-trivial. Finally prove $(\spadesuit)$ for this $D$. (Hint: First show
$$
D \times D \cong D,
$$
and then show $D$ satisfies $(\spadesuit)$.) Is this $D$ effectively given?

**EXERCISE 8.26.** Discuss in more detail the "pay-off" for $U$, namely the translation of "untyped" $\lambda$-calculus into $U$ as shown by the equations at the end of the lecture after the proof of 8.9. In particular show how the whole of the **typed** $\lambda$-calculus can be retranslated back into $U$ with the aid of projections. (Hint: Whenever you want to write
$$
f : D_a \to D_b,
$$
write instead

$$f = b \circ f \circ a,$$

where $a$, $b$ are finitary projections. Whenever you want to form a $\lambda$-abstraction

$$\lambda x^{D_a}.\,\sigma,$$

where $\sigma$ is of type $D_b$, instead form

$$\lambda x.\, b(\sigma'[a(x)/x]),$$

where $\sigma'$ is the further translation of $\sigma$ into untyped $\lambda$-calculus. Be sure to show that this result "has the right type" in the sense defined above.)

**EXERCISE 8.27.** (Suggested by James Donahue.)

Finite cartesian products of domains are formed by the $D_0 \times D_1$-construct we have used so often. The problem is to define — computably — some *infinite* cartesian products. In particular, as applied to the universal domain $U$, the combinator `sub` is to be regarded as a finitary projection of $U$ whose fixed points are exactly *all* the finitary projections. A map

$$d = \mathrm{sub} \circ d \circ \mathrm{sub}$$

can be regarded as a *polymorphic type* (because, whenever $t$ is a finitary projection ($=$ type), then so is $d(t)$). The *continuous product* of *all* these types would be the domain of all approximable functions $x$ such that

$$x(t) = d(t)(x(t))$$

for all types $t$. (Why does this equation mean that $x$ is in the product?) Define $\Pi$ as a combinator by

$$\Pi = \lambda d\,\lambda x\,\lambda t.\,\mathrm{sub}(d(\mathrm{sub}(t)))(x(\mathrm{sub}(t))).$$

Show that for $d$ a polymorphic type, $\Pi(d)$ is a type. (Hint: It is easy to check that $\Pi(d)$ is a projection; the problem is to show it is *finitary*.)
