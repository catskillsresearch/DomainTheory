# Fixed points and recursion

Having at this point a large supply of examples of domains (and further constructs of new domains), we now have to consider some other ways of defining functions — other than by explicit compositions of the very basic functions already mentioned. One of the most fruitful techniques is an infinitely iterated composition that is at the back of the idea of recursion. We will use the process over and over again in these lectures, not only to define new functions but also to define new domains. The heart of the matter lies in the so-called "Fixed-point Theorem":

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
The reader may have noticed that we used recursion in the proof of 4.1 (we had to define $f^n$ for all $n \in \mathbf{N}$). But 4.1 and 4.2 can be used to justify definitions by recursion on a large number of domains — definitions where the process of iteration is far from being as straightforward. In discussing this point, let us start with some basic examples.

**EXAMPLE 4.3.** The infinite generalization of our original example 1.2 is the system

$$
N = \{ \{n\} \mid n \in \mathbf{N} \} \cup \{ \mathbf{N} \}.
$$

The total elements are clearly in a one-one correspondence with the integers in $\mathbf{N}$. We can apply the construction of Exercise 3.16 to obtain a domain

$$
F = N^\infty.
$$

So we already know quite a bit about this domain — but it has a much more familiar presentation.

Let $\Phi$ be the set of all *finite partial functions* $\varphi \subseteq \mathbf{N} \times \mathbf{N}$ (that is, finite sets of ordered pairs of integers where, if $(n,m) \in \varphi$ and $(n,m') \in \varphi$, then $m = m'$). Define

$$
\uparrow \varphi = \{ \psi \in \Phi \mid \varphi \subseteq \psi \}.
$$

Consider the neighbourhood system

$$
F' = \{ \uparrow \varphi \mid \varphi \in \Phi \}.
$$

It is an easy exercise to show that $F$ and $F'$ are isomorphic and that the elements of these domains correspond exactly to the (possibly infinite) *partial functions* $\pi \subseteq \mathbf{N} \times \mathbf{N}$. Moreover, the *total* elements just correspond to the *total* functions $\tau : \mathbf{N} \to \mathbf{N}$ ("function" in the ordinary, set-theoretical sense of the word).

Another easy exercise is to show that the domains

$$
F \text{ and } (\mathbf{N} \to \mathbf{N})
$$

by our definitions are *NOT* isomorphic; though the two domains are closely related. We can define a mapping
$$
\mathrm{val} : F \times N \to N
$$

by the relationship

$$
\uparrow \phi \cup \{n\}\ \mathrm{val}\ \{m\} \quad \text{iff} \quad (n, m) \in \phi.
$$

(Of course $\mathrm{val}$ has to relate other neighbourhoods such as:

$$
\uparrow \phi \cup N\ \mathrm{val}\ N,
$$

but these are all.) It is then simple to prove that if $\pi \in |F|$ is regarded as a partial function $\pi : N \to N$ and if for $n \in N$ we define $\hat{n} \in |N|$ by

$$
\hat{n} = \{ \{n\}, N \},
$$

then we have

$$
\mathrm{val}(\pi, \hat{n}) = \widehat{\pi(n)}, \text{ if } \pi \text{ is defined at } n;
$$

$$
\qquad\qquad\qquad\qquad = \{N\}, \text{ otherwise.}
$$

(Remember that $\{N\} \in |N|$ is the "undefined" element.) This means that

$$
\mathrm{curry}(\mathrm{val}) : F \to (N \to N)
$$

is a one-one function on elements. (The rather slight trouble with $(N \to N)$ is that it has *more* elements than $F$.)

So much for the construction of $F$, we now wish to consider mappings

$$
f : F \to F
$$

and their uses. Consider the possibility

$$
f(\pi)(n) = 0, \qquad\qquad\qquad\qquad \text{if } n = 0;
$$

$$
\qquad\qquad\qquad = \pi(n-1) + n-1, \text{ if } n > 0.
$$

If $\pi$ were a total function, then $f(\pi)$ would be total. But if $\pi$ is partial, and if it is, say, undefined at $k$, then $f(\pi)$ becomes undefined at $k + 1$. Note that $f(\pi)$ is always defined at $0$. Note, too, that $f$ is an approximable mapping because it is completely determined by what it does to finite (partial) functions. Indeed,

$$
f(\pi) = \bigcup \{ f(\phi) \mid \phi \subseteq \pi \},
$$
where $\phi$ ranges over $\Phi$.

Well, we have proved that every approximable map of a domain into itself has a (*least*) fixed point. What is the least fixed point of this $f$? Suppose $\sigma = f(\sigma)$. Then $\sigma(0) = 0$, and

$$
\sigma(n + 1) = f(\sigma)(n + 1)
$$

$$
= \sigma(n) + n.
$$

By induction, then

$$
\sigma(n) = \sum_{i < n} i
$$

and $\sigma$ is a total function. (Therefore, $f$ has a *unique* fixed point.)

Actually, we can make the procedure more systematic by defining as fixed points elements of $(N \to N)$ rather than $F$. In the first place we have $\hat{0} \in |N|$, and from now on we will not distinguish between $n$ and $\hat{n}$. Next we have two mappings:

$$
\mathrm{succ}, \mathrm{pred} : N \to N
$$

where, as approximable mappings we have

$$
X\ \mathrm{succ}\ Y\ \mathrm{iff}\ \exists n \in N.\ n \in X\ \mathrm{and}\ n + 1 \in Y,
$$

$$
X\ \mathrm{pred}\ Y\ \mathrm{iff}\ \exists n \in N.\ n + 1 \in X\ \mathrm{and}\ n \in Y,
$$

for all $X, Y \in N$. This is *correct*, but what we mean in more understandable terms is:

$$
\mathrm{succ}(n) = n + 1;
$$

$$
\mathrm{pred}(n) = n - 1,\ \text{if}\ n > 0;
$$

$$
\qquad\qquad = \bot,\ \text{if}\ n = 0.
$$

Here, $n$ has been identified with $\hat{n} \in |N|$ and $\bot = \{N\} \in |N|$. Moreover, we have a mapping

$$
\mathrm{zero} : N \to T
$$

which is such that

$$
\mathrm{zero}(n) = \text{true, if } n = 0;
$$

$$
\qquad\qquad = \text{false, if } n > 0.
$$

The *structured domain*

$$
\langle N, 0, \mathrm{succ}, \mathrm{pred}, \mathrm{zero} \rangle
$$
can be called "THE domain of integers" for our present theory. We shall meet many other structured domains in the sequel.

Now the iterated summation function $\sigma$ can be completely characterized — as a map $\sigma : N \to N$ rather than as an element $\sigma \in |F|$ — by the following equation:

$$
\sigma(n) = \mathrm{cond}(\mathrm{zero}(n),\ 0,\ \sigma(\mathrm{pred}(n)) + \mathrm{pred}(n)).
$$

The only problem is that we have not defined $+ : N \times N \to N$. (A direct definition is left to the reader; general remarks are given later.) But $+$ could be any function of two variables in order to make the point about the form of the definition of $\sigma$. Remember

$$
\mathrm{cond} : T \times N \times N \to N,
$$

as defined in Exercise 3.26. We do not put cond in as part of the structure of $N$ because (as should be clear from 3.26) it is part of the structure of $T$.

The above equation for $\sigma$ is properly called a *functional equation*; it will be written as a fixed-point equation in Lecture V when we have the notation for the $\lambda$-calculus. $\square$

**EXAMPLE 4.4.** The domain $C$ of finite or infinite binary sequences mentioned in Exercise 2.21 may be regarded as a generalization of $N$. This can be made plain by saying how we wish to regard $C$ as a structured domain. To do this we should recall what $C$ is as a neighbourhood system. In the first place

$$
B = \{ \sigma\Sigma^* \mid \sigma \in \Sigma^* \}
$$

where $\Sigma = \{0, 1\}$. To form the system $C$ we have

$$
C = B \cup \{ \{\sigma\} \mid \sigma \in \Sigma^* \}.
$$

The total elements of $B$ correspond to *infinite binary sequences*; while the total elements of $C$ to *finite or infinite sequences*. To simplify notation let us write for $\sigma \in \Sigma^*$

$$
\sigma = \uparrow \{\sigma\} \quad \text{(a total element);}
$$

$$
\sigma\perp = \uparrow \sigma\Sigma^* \quad \text{(a partial element).}
$$
In other words we identify $\sigma$ with the corresponding total element in $|C|$.

We wish now to think of $C$ as a structured domain seen as a kind of generalization of $N$. The empty sequence $\Lambda$ will play the rôle of $0 \in |N|$; the map succ has two different analogues for $C$, however. Just as for $B$ we define for $x \in |C|$ and $\sigma \in \Sigma^*$:

$$
\sigma x = \{ Y \mid \sigma X \subseteq Y \text{ some } X \in x \},
$$

where of course now $X$ and $Y$ range over $C$. It should be checked that $\sigma \tau$ has the right meaning whether we think of $\tau \in \Sigma^*$ or $\tau \in |C|$. The two "successor" mappings we are looking for are

$$
x \mapsto 0x \quad \text{and} \quad x \mapsto 1x.
$$

All the maps $x \mapsto \sigma x$ can be obtained as compositions of these iterated as many times as needed.

Here are two questions which we now should ask:

<u>What plays the rôle of pred?</u>

The mapping will be called **tail**, and it is characterized by:

$$
\mathrm{tail}(0x) = x,
$$

$$
\mathrm{tail}(1x) = x, \text{ and}
$$

$$
\mathrm{tail}(\Lambda) = \perp.
$$

It is left to the reader to show that **tail** exists as an approximable mapping.

<u>What plays the rôle of zero?</u>

The answer is not unique, because in $C$ there are several distinctions that have to be made; in fact we will define three maps:

$$
\mathrm{empty}, \mathrm{zero}, \mathrm{one} : C \to T
$$

where the three maps take on truth-values to distinguish various kinds of elements in $|C|$ as follows:
$$
\begin{aligned}
\mathrm{empty}\,(\Lambda) &= \mathrm{true}, \\
\mathrm{empty}\,(0x) &= \mathrm{false}, \\
\mathrm{empty}\,(1x) &= \mathrm{false}, \\
\mathrm{zero}\,(\Lambda) &= \mathrm{false} \\
\mathrm{zero}\,(0x) &= \mathrm{true} \\
\mathrm{zero}\,(1x) &= \mathrm{false} \\
\mathrm{one}\,(\Lambda) &= \mathrm{false} \\
\mathrm{one}\,(0x) &= \mathrm{false} \\
\mathrm{one}\,(1x) &= \mathrm{true}.
\end{aligned}
$$

Again, it is an exercise to show these are approximable. The structured domain is therefore

$$
\langle C, \Lambda, 0, 1, \mathrm{tail}, \mathrm{empty}, \mathrm{zero}, \mathrm{one} \rangle.
$$

Note that we have changed the meaning of some of the symbols in passing from $N$ to $C$. Note too that there is a confusion between $0$ as an element and $0$ as the map $x \mapsto 0x$. There are just too few symbols! In any case this is only an example and not a philosophy of life, so the reader can be expected not to suffer too much.

An example of a definition of an *element* of $|C|$ by a fixed-point equation is:

$$
a = 0\,1\,a.
$$

This equation has one and only one solution in $|C|$, the infinite sequence that alternates 0's and 1's. Note that $a$ is also characterized by:

$$
a = 0101a.
$$

Another element is

$$
b = 010\,b,
$$

which is quite different from $a$.

An example of a *map* in $|C \to C|$ has the characterization

$$
\begin{aligned}
d(\Lambda) &= \Lambda \\
d(0x) &= 00d(x), \quad \text{and} \\
d(1x) &= 11d(x).
\end{aligned}
$$

We can write:
$$
\begin{aligned}
d(x) &= \mathrm{cond}(\mathrm{empty}(x),\, \Lambda, \\
&\qquad\qquad \mathrm{cond}(\mathrm{zero}(x),\, 00d(\mathrm{tail}(x)),\, 11d(\mathrm{tail}(x)))).
\end{aligned}
$$

As we shall see in due course, this can be regarded as a fixed-point definition of $d$.

An example of a map in $|C \times C \to C|$ was suggested in 2.21. We can write:

$$
\begin{aligned}
xy &= \mathrm{cond}(\mathrm{empty}(x),\, y, \\
&\qquad\qquad \mathrm{cond}(\mathrm{zero}(x),\, 0(\mathrm{tail}(x)\,y),\, 1(\mathrm{tail}(x)\,y))).
\end{aligned}
$$

It should be checked that this equation exactly characterizes the intended mapping. $\square$

The examples we have given with $N$ and $C$ are examples of definitions of functions by *recursion*. The literal meaning of “recursion” is “running backwards”, and a look at the equations for our examples will show that the functions are characterized by giving their values either *outright* (e.g. at $0$ or at $\Lambda$) or at *earlier* arguments (e.g. at $\mathrm{pred}(x)$ or at $\mathrm{tail}(x)$). The reader should keep in mind that a recursive “definition” is not really a definition in the sense of *explicit definition* but rather is a characterization; a theorem has to be proved to show that such functions exist. Now we have a general definition of domain and a general theorem on fixed points and a general construction of function-space domain; THEREFORE, we know that there are solutions to our equations PROVIDED THAT the variables range over elements of a domain and that the other, given functions that appear in the equations are already known to be approximable (continuous). This proviso is very important, and we shall remark on it time after time.

But, as is well known, recursion also can be done over sets like $\mathbf{N}$, and we should examine now the connection between the familiar kind of recursion and what we are doing over domains. Of course, one simple connection is already provided by the way we regard $\mathbf{N}$ as a subset of $N$. But there are other useful connections that can be employed in a way that may seem more direct.
**DEFINITION 4.5.** A structured set $\langle \mathbf{N}, 0, {}^+ \rangle$, where $0 \in \mathbf{N}$ and ${}^+ : \mathbf{N} \to \mathbf{N}$ is a unary function, is said to be a *model for Peano's Axioms* if the following conditions are satisfied:

(i) $0 \neq n^+$, for all $n \in \mathbf{N}$;

(ii) $n^+ = m^+$ implies $n = m$, for all $n, m \in \mathbf{N}$;

(iii) whenever $x \subseteq \mathbf{N}$ and $0 \in x$ and $x^+ \subseteq x$, then $x = \mathbf{N}$.

Here $x^+ = \{n^+ \mid n \in x\}$. $\square$

Clause (iii) is recognized as the principle of <u>mathematical induction</u> stated in terms of sets. We usually think of $\mathbf{N}$ as being "God given", and (i)–(iii) as known without question. Suppose God, however, decides to withdraw His set of integers and substitute another. We can ask: "Oh! Why did You take from us our beloved numbers? Why must we now live with these strange new beasts?" God will probably reply "Trust Me!" Perhaps we should in view of the theorem:

**THEOREM 4.6.** All models of Peano's Axioms are isomorphic.

*Proof:* There are several ways to give the proof, but, for the sake of illustration, an application of the fixed-point theorem is appropriate here. Let $\langle \mathbf{N}, 0, {}^+ \rangle$ be one model, and let $\langle \mathbf{M}, \square, {}^\# \rangle$ be another. Let $\mathbf{N} \times \mathbf{M}$ be the ordinary cartesian product of the two sets and let

$$
P(\mathbf{N} \times \mathbf{M})
$$

be the powerset (set of all subsets) of $\mathbf{N} \times \mathbf{N}$. As in Exercises 1.15 and 2.20, we regard this set of elements as a domain, whose finite elements are just the finite subsets of the given set $\mathbf{N} \times \mathbf{M}$. The following mapping on $u \subseteq \mathbf{N} \times \mathbf{M}$ is easily proved approximable:

$$
u \mapsto \{(0, \square)\} \cup \{(n^+, m^\#) \mid (n, m) \in u\}.
$$

(This assertion should be checked as an exercise.) We thus let $r$ be the (least) fixed point:

$$
r = \{(0, \square)\} \cup \{(n^+, m^\#) \mid (n, m) \in r\}.
$$
This $r \subseteq \mathbf{N} \times \mathbf{M}$ as a binary relation will turn out to be a one-one correspondence giving the required isomorphism.

First of all we see by construction that

(i) $0 \ r \ \square$;

(ii) $n \ r \ m$ implies $n^+ \ r \ m^\#$.

So, if $r$ proves to be a one-one correspondence, it will then be the desired isomorphism. Now, the two sets shown in the equation

$$
\{(0, \square)\} \cap \{(n^+, m^\#) \mid (n, m) \in r\} = \emptyset
$$

are disjoint by virtue of axiom 4.5(i). Therefore, $0$ in $\mathbf{N}$ corresponds by $r$ to one and only one element of $\mathbf{M}$, namely the element $\square$. Let $x \subseteq \mathbf{N}$ be the set of all elements of $\mathbf{N}$ corresponding by $r$ to a unique element of $\mathbf{M}$. We have just shown $0 \in x$. Suppose $n \in x$, and let $m \in \mathbf{M}$ be the unique element with $n \ r \ m$. Now $n^+ \ r \ m^\#$ holds, so $n^+$ corresponds to at least one element of $\mathbf{M}$. If $n^+ \ r \ k$ also holds, then since $(n^+, k) \neq (0, \square)$, the fixed-point equation implies

$$
n^+ = n_0^+ \quad \text{and} \quad k = m_0^\#
$$

for some $(n_0, m_0) \in r$. By axiom 4.5(ii), $n = n_0$, and, by uniqueness (remember $n \in x$), $m = m_0$; thus, $m^\#$ is the unique correspondent for $n^+$. We have proved $n^+ \in x$. Therefore, $x^+ \subseteq x$; so by axiom 4.5(iii), $x = \mathbf{N}$ holds. Otherwise said, every element in $\mathbf{N}$ corresponds to a unique element of $\mathbf{M}$.

Note that the rôles of $\mathbf{N}$ and $\mathbf{M}$ are completely symmetric, *and* they satisfy the same axioms as structured sets. It follows, then, that every element of $\mathbf{M}$ corresponds to a unique element of $\mathbf{N}$. The proof that $r$ is a one-one correspondence is now complete. $\square$

**EXERCISES**

**EXERCISE 4.7.** Formula 4.2(iii) shows how to find the *least* fixed point of $f : D \to D$. Suppose on the other hand that $a \in |D|$ is such that $a \subseteq f(a)$. Will there be a fixed point $x = f(x)$ with $a \subseteq x$?
(Hint: How do we know $\bigsqcup_{n=0}^{\infty} f^n(\bot) \in |D|$ ?)

**EXERCISE 4.8.** Suppose $f : D \to D$ and $S \subseteq |D|$ are such that

(i) $\bot \in S$;

(ii) $x \in S$ always implies $f(x) \in S$;

(iii) whenever $\{x_n\}_{n=0}^{\infty} \subseteq S$ and $x_n \sqsubseteq x_{n+1}$ for all $n$, then $\bigsqcup_{n=0}^{\infty} x_n \in S$.

Conclude that $\mathrm{fix}(f) \in S$. (This could be called the principle of *fixed-point induction*.) Apply the method to a set of the form

$$
S = \{x \in |D| \mid a(x) = b(x)\},
$$

where $a, b : D \to D$ are approximable, and where we know $a(\bot) = b(\bot)$, and $f \circ a = a \circ f$ and $f \circ b = b \circ f$.

**EXERCISE 4.9.** Show that there is an approximable operator

$$
\Psi : ((D \to D) \to D) \to ((D \to D) \to D)
$$

such that for $\theta : (D \to D) \to D$ and $f : D \to D$ we have

$$
\Psi(\theta)(f) = f(\theta(f)).
$$

Prove further that $\mathrm{fix} : (D \to D) \to D$ is the *least* fixed point of $\Psi$.

**EXERCISE 4.10.** Given a domain $D$ and an element $a \in |D|$, construct a domain $D_a$ where

$$
|D_a| = \{x \in |D| \mid x \sqsubseteq a\}.
$$

Show that if $f : D \to D$ is approximable, then $f$ can be restricted to an approximable map $f' : D_{\mathrm{fix}(f)} \to D_{\mathrm{fix}(f)}$ where $f'(x) = f(x)$ for all $x \in |D_{\mathrm{fix}(f)}|$. How many fixed points does $f'$ have in $|D_{\mathrm{fix}(f)}|$?
**EXERCISE 4.11.** (Suggested by G. Plotkin). We can regard $\mathrm{fix}$ as assigning a fixed-point operator to each domain $D$. Show that $\mathrm{fix}$ is uniquely determined by the following general conditions on an assignment $D \rightsquigarrow F_D$:

(i) $F_D : (D \to D) \to D$;

(ii) $F_D(f) = f(F_D(f))$ for all $f : D \to D$;

(iii) whenever $f_0 : D_0 \to D_0$ and $f_1 : D_1 \to D_1$ are given and $h : D_0 \to D_1$ is such that $h(\perp) = \perp$ and $h \circ f_0 = f_1 \circ h$, then $h(F_{D_0}(f_0)) = F_{D_1}(f_1)$.

(Hint: Apply 4.7 to prove $\mathrm{fix}$ satisfies (iii). In the other direction use 4.10.)

**EXERCISE 4.12.** Need an approximable $f : D \to D$ have a maximum fixed point? Give an example where there are many fixed points.

**EXERCISE 4.13.** The proof of 4.1 uses the integers, whereas the proof of 4.6 uses 4.1. There is a hint of circularity here! It can be eliminated by the following steps:

(1) If a domain $D$ has an element $a$ where, for $f : D \to D$, the relation $f(a) \sqsubseteq a$ holds, then the least fixed point can be defined by

$$
\mathrm{fix}(f) = \bigcap \{ x \in |D| \mid f(x) \sqsubseteq x \}.
$$

Note that $\mathrm{fix}(f) \sqsubseteq a$. (Hint: Remark that by 1.17 the formula gives a well-defined element. Call the element $b$. Prove that $f(b) \sqsubseteq b$ by showing that $f(b) \sqsubseteq x$ whenever $f(x) \sqsubseteq x$. Then note that $f(f(b)) \sqsubseteq f(b)$ so that $b \sqsubseteq f(b)$ also. Conclude $b = \mathrm{fix}(f)$ as least fixed point.)

(2) Remark that this proof uses only the monotonicity property of $f : |D| \to |D|$. Remark, too, that (1) can always be applied to power-set domains $PA$ for any set $A$.

(3) Review the proof of 4.6 and establish by a fixed-point method that for any structured set $\langle Z, z, \cdot \rangle$ there is a unique function $s : \mathbf{N} \to Z$ such that

(i) $s(0) = z$;

(ii) $s(n^+) = s(n)^\cdot$, for $n \in \mathbf{N}$.

(4) Employ (3) for the proof of 4.1 by identifying $\langle \mathbf{N}, 0, {}^+ \rangle$.
**EXERCISE 4.14.** Need a monotone function $f : PA \to PA$ always have a *maximum* fixed point?

**EXERCISE 4.15.** (For set theorists.) Let $f : |D| \to |D|$ be a monotone function on (the elements of) a domain. Show that $f$ has a *maximal* fixed point (i.e. a fixed point that cannot be extended to a larger fixed point). (Hint: By Zorn's Lemma consider a maximal chain

$$
C \subseteq \{ x \in |D| \mid x \sqsubseteq f(x) \},
$$

and use 2.11 to remark that $\bigsqcup C \in |D|$.) Now argue that $f$ has a <u>least</u> fixed point.

**EXERCISE 4.16.** (For fixed-point nuts). Show that a monotone function as in 4.15 has an "optimal" fixed point in the sense that it is the greatest fixed point <u>below</u> all the maximal fixed points and at the same time it is the largest fixed point consistent with all other fixed points. *Consistency* for sets of elements means having a common upper bound. (Hint: Follow these steps:

(1) Show that any non-empty set $S$ of fixed points has a largest fixed point <u>below</u> by using the formula

$$
f(\bigcap S) \sqsubseteq \bigcap S
$$

and finding the least fixed point over $\bigcap S$.

(2) Letting $a$ be the fixed point of (1) constructed from the set of maximal fixed points, remark that $a$ is consistent with any other fixed point $x = f(x)$, since $x$ can be extended to a maximal one. Suppose $b$ is consistent with all fixed points, then $b \sqsubseteq y$ if $y$ is maximal. (Why?).)

**EXERCISE 4.17.** (For algebraists). Suppose $\langle S, 1, \cdot \rangle$ is a semi-group with unit (sometimes called a monoid). Remark that $PS$ is a domain. For $a, b \in S$, what is the least $x \in PS$ such that

$$
x = \{1\} \cup \{a, b\} \cup x \cdot x,
$$

where in general for $x, y \subseteq S$

$$
x \cdot y = \{ t \cdot u \mid t \in x \text{ and } u \in y \}?
$$

Need the fixed point be unique?
**EXERCISE 4.18.** In Example 4.3 there are many unproved assertions about $N$ and $F$. These should be checked. In particular, the isomorphism theorem of 4.6 could be proved by constructing a simple domain $M$ from $\mathbf{M}$ in the way $N$ is constructed from $\mathbf{N}$.

**EXERCISE 4.19.** There are many unproved assertions in Example 4.4! In particular discuss "Peano's Axioms" for $\{0,1\}^*$. Show, moreover, that $\mathrm{one} : C \to T$ can be defined from the rest of the structure by a fixed-point equation.

**EXERCISE 4.20.** For approximable $f, g : D \to D$ prove that

$$
\mathrm{fix}(f \circ g) = f(\mathrm{fix}(g \circ f)).
$$

**EXERCISE 4.21.** Show that the less-than-or-equal-to relation $\ell \subseteq \mathbf{N} \times \mathbf{N}$ is uniquely determined by the fixed point equation

$$
\ell = \{(n,n) \mid n \in \mathbf{N}\} \cup \{(n, m^+) \mid (n, m) \in \ell\}.
$$

Consider the structured set $\langle P\mathbf{N}, \mathbf{N}, {}^+ \rangle$ where, as before, $x^+ = \{n^+ \mid n \in x\}$.

What is the unique function $[\cdot] : \mathbf{N} \to P\mathbf{N}$ given by 4.13(3)? Prove that the structures $\langle \mathbf{N}, 0, {}^+ \rangle$ and $\langle [m], m, {}^+ \rangle$ are uniquely isomorphic for each $m \in \mathbf{N}$, and connect the isomorphism with ordinary addition of integers. Can the same be done for multiplication? (Hint: Consider the fixed-point equation

$$
n \cdot \mathbf{N} = \{0\} \cup \{n + m \mid m \in n \cdot \mathbf{N}\},
$$

where $n \in \mathbf{N}$ is fixed.)

**EXERCISE 4.22.** Suppose $\mathbf{N}^*$ is a structured set satisfying only axioms (i) and (ii) of 4.5. Must there be a subset $\mathbf{N} \subseteq \mathbf{N}^*$ that satisfies (i), (ii), and (iii)? (Hint: Use a least fixed point in $P\mathbf{N}^*$.) (For set theorists): How do we know from the axioms of set theory that there exists such a set $\mathbf{N}^*$?
**EXERCISE 4.23.** (Suggested by S. Eilenberg). Suppose $f : \mathcal{D} \to \mathcal{D}$ is approximable on a given domain $\mathcal{D}$. Suppose $a_n : \mathcal{D} \to \mathcal{D}$ is a sequence of approximable maps where

(i) $a_0(x) = \bot$, for all $x \in |\mathcal{D}|$;

(ii) $a_n \sqsubseteq a_{n+1}$ in $\mathcal{D} \to \mathcal{D}$, for all $n \in \mathbf{N}$;

(iii) $\bigsqcup_{n=0}^{\infty} a_n = I_{\mathcal{D}}$ in $\mathcal{D} \to \mathcal{D}$;

(iv) $a_{n+1} \circ f = a_{n+1} \circ f \circ a_n$, for all $n \in \mathbf{N}$.

Prove that $f$ has a unique fixed point. (Hint: Show that if $x = f(x)$, then $a_n(x) \sqsubseteq a_n(\mathrm{fix}(f))$ for all $n \in \mathbf{N}$ by induction on $n$.)

**EXERCISE 4.24.** (For set theorists). Let $f : A \to B$ and $g : B \to A$ be one-one functions (into, not necessarily onto!) Prove the Schroeder - Bernstein theorem to the effect that there exists a one-one correspondence $h : A \leftrightarrow B$. (Hint: (Suggested by A. Tarski). By the fixed-point theorem find $X \subseteq A$ where

$$
X = (A - g(B)) \cup g(f(X)),
$$

where $f(X) =$ the image of the set $X$ under the function $f$. Define $h \subseteq A \times B$ as a union of two restrictions:

$$
h = f \upharpoonright X \cup g^{-1} \upharpoonright (A - X).
$$

A picture helps.)

**EXERCISE 4.25.** Perhaps the domains $\mathbf{N}$ and $C$ are not exactly analogous? $C$ was based on $\{0,1\}$ as the underlying set of tokens. Construct a system $C_1$ based on $\{1\}^*$ (= finite strings of 1's) with neighbourhoods:

$$
C_1 = \{\, \{1^m \mid m > n\} \mid n \in \mathbf{N} \,\} \cup \{\, \{1^n\} \mid n \in \mathbf{N} \,\}.
$$

What structure should be put on $C_1$ strictly analogous to that on $C (= C_2)$? What kinds of approximable maps relate $\mathbf{N}$, $C_1$, and $C_2$? Draw some pictures.

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_bot_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_bot_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_master.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_master.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/N_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/T.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/T.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN_natElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/constLiftN_natElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN_univ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/memN_univ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/mem_natElem_iff.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/mem_natElem_iff.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/natElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/natElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/nestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/nestedOrDisjoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_natElem_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_natElem_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_natElem_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_natElem_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_succMap_natElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predMap_succMap_natElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predVal.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/predVal.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/singleton_nat_inj.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/singleton_nat_inj.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/singleton_ne_univ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/singleton_ne_univ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap_natElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/succMap_natElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/univ_ne_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/univ_ne_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroElt.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroElt.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_natElem_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_natElem_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_natElem_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroMap_natElem_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroVal.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example43/zeroVal.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C_master.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C_master.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/C_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/altElt.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/altElt.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/altElt_eq.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/altElt_eq.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap_strBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap_strBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap_strElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/consMap_strElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_cone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_cone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_prepend.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_prepend.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/memC_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/nestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/nestedOrDisjoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_subset_self.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/prepend_subset_self.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/singleton_cone_nd.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/singleton_cone_nd.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/singleton_subset_cone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/singleton_subset_cone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/strBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/strBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Example44/strElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Example44/strElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/fixAbove.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/fixAbove.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/fixAbove_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/fixAbove_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/fixAbove_least.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/fixAbove_least.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/iterFrom.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/iterFrom.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/iterFrom_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/iterFrom_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/iterFrom_step.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/iterFrom_step.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/iterFrom_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/iterFrom_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/iterFrom_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/iterFrom_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/le_fixAbove.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise407/le_fixAbove.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fixElement_eq_supChain.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fixElement_eq_supChain.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fix_induction.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fix_induction.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fix_induction_eq.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/fix_induction_eq.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_monotone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/iterElem_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/mem_supChain.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/mem_supChain.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/supChain.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise408/supChain.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_apply.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_apply.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_fix.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_fix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_least.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/bigPsi_least.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/fix_eq_fixElement_bigPsi.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/fix_eq_fixElement_bigPsi.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/toApproxMap_toFilter_fixMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise409/toApproxMap_toFilter_fixMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_restrict.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/embed_restrict.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/fixElement_below_unique.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/fixElement_below_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/le_of_embed_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/le_of_embed_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relIso.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relIso.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap_toElementMap_embed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap_toElementMap_embed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap_unique_fixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relMap_unique_fixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem_master.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem_master.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/relSystem_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/restrict.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/restrict.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/restrict_embed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise410/restrict_embed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/fixElement_uniform.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/fixElement_uniform.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/fix_unique_of_uniform.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/fix_unique_of_uniform.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/inclMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/inclMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/inclMap_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/inclMap_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/inclMap_intertwine.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/inclMap_intertwine.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/inclMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/inclMap_toElementMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/iterElem_le_fixElement.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise411/iterElem_le_fixElement.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412/elemOne_not_le_elemZero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412/elemOne_not_le_elemZero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412/elemZero_not_le_elemOne.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412/elemZero_not_le_elemOne.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412/idMap_fixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412/idMap_fixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412/no_greatest_fixedPoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise412/no_greatest_fixedPoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/exists_unique_nat_rec.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/exists_unique_nat_rec.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/mem_preFix.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/mem_preFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_le_preFix.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_le_preFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_least.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_least.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_preFix.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_preFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/nat_iterate_unique.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/nat_iterate_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/preFix.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/preFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/f_subset_lfpSet.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/f_subset_lfpSet.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/gfpSet.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/gfpSet.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/gfpSet_greatest.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/gfpSet_greatest.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/gfpSet_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/gfpSet_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/gfpSet_subset_f.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/gfpSet_subset_f.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/lfpSet.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/lfpSet.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/lfpSet_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/lfpSet_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/lfpSet_least.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/lfpSet_least.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/lfpSet_subset.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/lfpSet_subset.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/subset_gfpSet.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise414/subset_gfpSet.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/chainUnion_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/chainUnion_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/exists_least_fixedPoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/exists_least_fixedPoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/exists_maximal_fixedPoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/exists_maximal_fixedPoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/f_sInf_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/f_sInf_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_consistent.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_consistent.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_le_sInf.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_le_sInf.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F_monotone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F_one_one_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F_one_one_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F_univ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F_univ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/a_mem_F.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/a_mem_F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/b_mem_F.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/b_mem_F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/base_subset_F.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/base_subset_F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/fixedPoint_not_unique.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/fixedPoint_not_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/leastSolution_eq.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/leastSolution_eq.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/lfpSet_eq_closure.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/lfpSet_eq_closure.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/one_mem_F.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/one_mem_F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/preFixSubmonoid.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/preFixSubmonoid.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/self_mul_subset_F.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/self_mul_subset_F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/element_classification.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/element_classification.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/natElem_injective.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/natElem_injective.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/natElem_zero_ne_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/natElem_zero_ne_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/not_N_mem_empty.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/not_N_mem_empty.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/succMap_injective.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/succMap_injective.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/zero_ne_succMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise418/zero_ne_succMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/Basic/notation14.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/Basic/notation14.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/Basic/notation15.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/Basic/notation15.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/T.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/T.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/condT_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/condT_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/cone_ne_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/cone_ne_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/emptyMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/emptyMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/emptyMap_strBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/emptyMap_strBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/emptyMap_strElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/emptyMap_strElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/headValC.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/headValC.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/headValC_bot_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/headValC_bot_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/headValC_false.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/headValC_false.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/headValC_nil.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/headValC_nil.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/headValC_true.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/headValC_true.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/liftC.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/liftC.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/liftC_strBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/liftC_strBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/liftC_strElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/liftC_strElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/not_cone_subset_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/not_cone_subset_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/oneDef.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/oneDef.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/oneMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/oneMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/oneMap_strBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/oneMap_strBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/oneMap_strElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/oneMap_strElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/one_def_strBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/one_def_strBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/one_def_strElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/one_def_strElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/peano_cons_disjoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/peano_cons_disjoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/peano_cons_injective.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/peano_cons_injective.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/peano_induction.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/peano_induction.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/peano_nil_ne_cons.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/peano_nil_ne_cons.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/zeroMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/zeroMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/zeroMap_strBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/zeroMap_strBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/zeroMap_strElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise419/zeroMap_strElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise420.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise420.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise420/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise420/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise420/comp_fixElement_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise420/comp_fixElement_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise420/fixElement_comp_comm.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise420/fixElement_comp_comm.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_apply.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_apply.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp_monotone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp_unique.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leRel.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leRel.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leRel_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leRel_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mem_fixedPoint_iff.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mem_fixedPoint_iff.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp_lfp_eq_multiples.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp_lfp_eq_multiples.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp_monotone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/succImage.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/succImage.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_unique.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/Nat'.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/Nat'.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/exists_peano_submodel.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/exists_peano_submodel.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/genOp.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/genOp.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/genOp_monotone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/genOp_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/genOp_nats.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/genOp_nats.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/natPeano.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/natPeano.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/nats.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/nats.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/nats_induction.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/nats_induction.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/peanoSub.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/peanoSub.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/subSucc.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/subSucc.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/subZero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/subZero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/succ_mem_nats.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/succ_mem_nats.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/zero_mem_nats.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise422/zero_mem_nats.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise423.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise423.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise423/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise423/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise423/f_unique_fixedPoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise423/f_unique_fixedPoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/g_f_mem_of_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/g_f_mem_of_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/g_sbFun_not_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/g_sbFun_not_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/mem_range_of_not_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/mem_range_of_not_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_injective.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_injective.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_surjective.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_surjective.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbOp.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbOp.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbOp_monotone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbOp_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbSet.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbSet.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbSet_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbSet_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/schroeder_bernstein.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/schroeder_bernstein.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/schroeder_bernstein_equiv.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/schroeder_bernstein_equiv.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1_master.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1_master.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap_oneBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap_oneBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap_oneElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap_oneElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/infElt.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/infElt.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/infElt_eq.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/infElt_eq.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_shift.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_shift.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_tail.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_tail.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_univ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_univ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/mem_tail.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/mem_tail.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/nestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/nestedOrDisjoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/oneBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/oneBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/oneElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/oneElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1_natElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1_natElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_tail.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_tail.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/singleton_tail_nd.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/singleton_tail_nd.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/tail.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/tail.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/tail_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/tail_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/comp_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/comp_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/exists_principal_iterMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/exists_principal_iterMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_eq_iSupDirected.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_eq_iSupDirected.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_le_of_toElementMap_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_le_of_toElementMap_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixElement_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_eq_iSup.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_eq_iSup.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_fixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_fixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_least.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_least.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap_principal.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap_principal.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap_toFilter.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_toElementMap_toFilter.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_unique.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/fixMap_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem_eq_iterate.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem_eq_iterate.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterElem_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_mono_map.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_mono_map.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iterMap_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iter_comm.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/iter_comm.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/mem_fixElement.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/mem_fixElement.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/mem_iterElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/mem_iterElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/rel_master_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/rel_master_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/rel_master_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/rel_master_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/toElementMap_fixElement.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem41/toElementMap_fixElement.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/Graph.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/Graph.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/Graphu2eswap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/Graphu2eswap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/PeanoModel.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/PeanoModel.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/exists_unique_left.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/exists_unique_left.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/exists_unique_right.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/exists_unique_right.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/graph_succ_right.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/graph_succ_right.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/graph_zero_right.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/graph_zero_right.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/peano_models_isomorphic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Theorem46/peano_models_isomorphic.lean)
