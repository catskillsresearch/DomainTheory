# Domain constructs

Having now seen a number of domains presented through their neighbourhood systems, we need next to introduce general constructs for forming new domains from old. There are an unlimited number of such constructs (technically called *functors*), but we have time only to single out a few of the more important ones. Outstanding among all of them is the notion of product of systems, which in our chosen category has all the expected properties. For the time being in order to simplify notation we assume of the underlying sets $\Delta_0$ and $\Delta_1$ of systems $\mathcal{D}_0$ and $\mathcal{D}_1$ that they are disjoint. There is no loss of generality as $\mathcal{D}_1$ can always be replaced by an isomorphic system disjoint from $\mathcal{D}_0$ in the required sense.

**DEFINITION 3.1.** Let neighbourhood systems $\mathcal{D}_0$ and $\mathcal{D}_1$ be given over disjoint sets $\Delta_0$ and $\Delta_1$. The *product system* over $\Delta_0 \cup \Delta_1$ is defined by:

$$
\mathcal{D}_0 \times \mathcal{D}_1 = \{X \cup Y \mid X \in \mathcal{D}_0 \text{ and } Y \in \mathcal{D}_1\}.
$$

For elements $x \in |\mathcal{D}_0|$ and $y \in |\mathcal{D}_1|$ we also define:

$$
\langle x, y \rangle = \{X \cup Y \mid X \in x \text{ and } Y \in y\}.
$$

$\square$

**PROPOSITION 3.2.** The construct $\mathcal{D}_0 \times \mathcal{D}_1$ always gives a neighbourhood system where for elements $x, x' \in |\mathcal{D}_0|$ and $y, y' \in |\mathcal{D}_1|$ we have

(i) $\langle x, y \rangle \subseteq \langle x', y' \rangle$ iff $x \subseteq x'$ and $y \subseteq y'$.

Moreover, there is a one-one correspondence between the elements of $|\mathcal{D}_0 \times \mathcal{D}_1|$ and pairs of elements of $|\mathcal{D}_0|$ and $|\mathcal{D}_1|$ since all elements of $|\mathcal{D}_0 \times \mathcal{D}_1|$ are of the form $\langle x, y \rangle$.

*Proof:* Owing to the disjointness of $\Delta_0$ and $\Delta_1$, we note that for $X, X' \in \mathcal{D}_0$ and $Y, Y' \in \mathcal{D}_1$ we have

$$
\text{(1) } X \cup Y \subseteq X' \cup Y' \text{ iff } X \subseteq X' \text{ and } Y \subseteq Y'.
$$

Thus, $\{X \cup Y, X' \cup Y'\}$ is consistent in $\mathcal{D}_0 \times \mathcal{D}_1$ iff $\{X, X'\}$ is
consistent in $\mathcal{D}_0$ and $\{Y, Y'\}$ is consistent in $\mathcal{D}_1$. In the consistent case we find

$$
\text{(2)}\qquad (X \cup Y) \cap (X' \cup Y') = (X \cap X') \cup (Y \cap Y'),
$$

and so $\mathcal{D}_0 \times \mathcal{D}_1$ is closed under consistent intersection. As $\Delta_0 \cup \Delta_1 \in \mathcal{D}_0 \times \mathcal{D}_1$, it is certainly a neighbourhood system.

It is easy to check by the previous calculations that $\langle x, y \rangle \in |\mathcal{D}_0 \times \mathcal{D}_1|$ if $x \in |\mathcal{D}_0|$ and $y \in |\mathcal{D}_1|$. The proof of 3.2(i) follows directly from the definition and (1).

Suppose $z \in |\mathcal{D}_0 \times \mathcal{D}_1|$. Define as a temporary notation:

$$
z_0 = \{X \in \mathcal{D}_0 \mid X \cup \Delta_1 \in z\}, \quad \text{and} \quad z_1 = \{Y \in \mathcal{D}_1 \mid \Delta_0 \cup Y \in z\}.
$$

Clearly, both $z_0 \in |\mathcal{D}_0|$ and $z_1 \in |\mathcal{D}_1|$. In view of the formula

$$
\text{(3)}\qquad (X \cup \Delta_1) \cap (\Delta_0 \cup Y) = X \cup Y,
$$

we can calculate that

$$
z = \langle z_0, z_1 \rangle.
$$

Moreover, if $z = \langle x, y \rangle$, then $\langle x, y \rangle_0 = x$ and $\langle x, y \rangle_1 = y$.

The one-one correspondence required is thus established. $\square$

There is more going on in the proof of 3.2 than just a one-one correspondence between elements and pairs. The extra information is best formalized by introducing a notation for mappings.

**DEFINITION 3.3.** *Projection mappings*

$$
p_0 : \mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}_0 \quad \text{and} \quad p_1 : \mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}_1
$$

are defined as relations where

$$
(X \cup Y)\ p_0\ X' \text{ iff } X \subseteq X', \quad \text{and} \quad (X \cup Y)\ p_1\ Y' \text{ iff } Y \subseteq Y'
$$

hold for all $X, X' \in \mathcal{D}_0$ and $Y, Y' \in \mathcal{D}_1$. Given $f : \mathcal{D}_2 \to \mathcal{D}_0$ and $g : \mathcal{D}_2 \to \mathcal{D}_1$, the *paired mapping*

$$
\langle f, g \rangle : \mathcal{D}_2 \to \mathcal{D}_0 \times \mathcal{D}_1
$$

is defined as a relation where

$$
Z\ \langle f, g \rangle\ (X \cup Y) \text{ iff } Z\ f\ X \text{ and } Z\ g\ Y
$$

holds for all $X \in \mathcal{D}_0$, $Y \in \mathcal{D}_1$, and $Z \in \mathcal{D}_2$. $\square$
**PROPOSITION 3.4.** The mappings $p_0$, $p_1$ and $\langle f, g \rangle$ are approximable mappings, provided $f$ and $g$ are, and we have:

(i) $p_0 \circ \langle f, g \rangle = f$ and $p_1 \circ \langle f, g \rangle = g$.

Moreover, for $z \in |\mathcal{D}_0 \times \mathcal{D}_1|$, we have:

(ii) $p_0(z) = z_0$ and $p_1(z) = z_1$,

in the notation of the proof of 3.2. Further if $h : \mathcal{D}_2 \to \mathcal{D}_0 \times \mathcal{D}_1$ is any approximable mapping, then

(iii) $h = \langle p_0 \circ h, p_1 \circ h \rangle$.

Moreover, for all $w \in |\mathcal{D}_2|$, we have:

(iv) $\langle f, g \rangle(w) = \langle f(w), g(w) \rangle$,

where again on the right-hand side the notation of the proof of 3.2 is used. $\square$

The proof of this result is left as an exercise. Note the consequence that there is a one-one correspondence between pairs of approximable mappings $f : \mathcal{D}_2 \to \mathcal{D}_0$ and $g : \mathcal{D}_2 \to \mathcal{D}_1$ and mappings $h : \mathcal{D}_2 \to \mathcal{D}_0 \times \mathcal{D}_1$. It is clear that we generalize all this to products

$$
\mathcal{D}_0 \times \mathcal{D}_1 \times \cdots \times \mathcal{D}_{n-1}
$$

of several systems.

The product construct also neatly explains functions of several variables. In Exercise 2.19 we used the informal notation

$$
f : \mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}_2
$$

and suggested regarding $f$ as a ternary relation

$$
X, Y\ f\ Z.
$$

But now with $\mathcal{D}_0 \times \mathcal{D}_1$ given an independent meaning, all we have to do is to regard $f$ as a binary relation with

$$
(X, Y)\ f\ Z
$$

equivalent to the old relationship. We can also employ an element-wise notation as in $f(\langle x, y \rangle)$, which can more easily be written $f(x, y)$. Similar remarks apply to functions of more than two arguments.
We have discussed several times what it means for a function $f(x)$ to come from an approximable mapping. It is interesting to ask the analogous question for functions of several arguments.

**THEOREM 3.5.** An elementwise function
$$f : |D_0 \times D_1| \to |D_2|$$
of two arguments comes from an approximable mapping iff for each fixed $a \in |D_0|$ and each fixed $b \in |D_1|$ the transformations
$$x \mapsto f(x, b) \quad \text{and} \quad y \mapsto f(a, y)$$
come from approximable mappings of one argument.

*Proof:* As this is the first time we have had to deal with constants in functions, a lemma is useful.

**LEMMA 3.6.** Given $b \in |D_1|$, the constant function
$$b : |D_0| \to |D_1|$$
where $b(x) = b$ for all $x \in |D_0|$, comes from the approximable mapping such that
$$X\ b\ Y \quad \text{iff} \quad Y \in b,$$
for all $X \in D_0$ and $Y \in D_1$. $\square$

There is no real confusion here in using “$b$” both for function and value. Returning, then, to the proof of 3.5, we see that the reason that $x \mapsto f(x, b)$ comes from an approximable mapping is that the mapping in question is the composition of two approximable mappings, namely $f \circ \langle I_{D_0}, b \rangle$. Clearly we can interchange the rôles of $D_0$ and $D_1$ to get at $y \mapsto f(a, y)$.

Conversely, assume that both these functions come from approximable mappings no matter the choice of $a$ and $b$. Clearly the mapping to determine $f$ is the relation from $X \cup Y$ to $Z$ where
$$Z \in f(\uparrow X, \uparrow Y) = f(\uparrow(X \cup Y)).$$
To prove that this determines $f$ we calculate by the formula of Exercise 2.9:
$$
\begin{aligned}
f(x, y) &= \bigcup \{ f(\uparrow X, y) \mid X \in x \} \\
&= \bigcup \{ \bigcup \{ f(\uparrow X, \uparrow Y) \mid Y \in y \} \mid X \in x \} \\
&= \bigcup \{ f(\uparrow X, \uparrow Y) \mid X \in x \text{ and } Y \in y \} \\
&= \bigcup \{ f(\uparrow (X \cup Y)) \mid (X \cup Y) \in \langle x, y \rangle \}.
\end{aligned}
$$

And, again by 2.9, this is what was needed. $\square$

Said more informarily, a function of several arguments is approximable in all the variables *jointly* if it is approximable in each of the variables *separately*.

The type of argument used in 3.5 in the first half of the proof also provides a generalization of 2.6 to functions of several arguments. When we form a function like

$$
f(g(x, z, \ldots), h(y, x, \ldots), k(z, w, \ldots), \ldots)
$$

from given functions $f, g, h, k, \ldots$; we call the process *substitution*.

**PROPOSITION 3.7.** The functions of several arguments between domains coming from approximable mappings are closed under substitution.

*Proof:* An example will establish the method. Suppose there are four variables involved taking values in domains provided by systems $D_0, D_1, D_2, D_3$. We might have a substitution like:

$$
f(g(x_0, x_1), h(x_1, x_2), k(x_3, x_0, x_2)).
$$

Here it might be that the values of the functions inside come from quite other systems; for instance,

$$
k : D_3 \times D_0 \times D_2 \to D_4
$$

might be possible. By using projections

$$
p_i : D_0 \times D_1 \times D_2 \times D_3 \to D_i,
$$

where $i < 4$, we can assure that we have several functions all on the same product; thus,

$$
k \cdot \langle p_3, p_0, p_2 \rangle : D_0 \times D_1 \times D_2 \times D_3 \to D_4.
$$

Now no matter on what domains $f$ is defined, the following composition makes sense:
$$
f \circ \langle g \circ \langle p_0, p_1 \rangle, h \circ \langle p_1, p_2 \rangle, k \circ \langle p_3, p_0, p_2 \rangle \rangle ;
$$

and in fact this is the desired function. Writing it this way makes it clear that the function comes from an approximable mapping: we apply 3.3 (generalized, of course, to products with several terms) to construe the parts between brackets $\langle$ and $\rangle$ as approximable mappings, and then by this trick the composition $\circ$ is the ordinary composition of 2.6. $\square$

It has to be admitted that there is a slight point overlooked in forming products like $D \times D$ with two identical domains. This is discussed in Exercise 3.14, invoking explicit isomorphisms.

The construct that makes the whole theory of domains work so smoothly is the function-space construct: it is possible to regard functions as *objects* which form a domain. Look back at Definition 2.1 and compare it with the original definition of element in 1.6. There are obvious formal similarities, except that filters are sets of neighbourhoods and mappings are sets of pairs of neighbourhoods (relations). But as we saw in 1.10 it is possible to turn the filters into tokens via a simple definition of neighbourhood. We apply the same kind of definition to the mappings.

**DEFINITION 3.8.** Given neighbourhood systems $D_0$ and $D_1$, the *function space* $(D_0 \to D_1)$ is the system whose set of tokens is the set of approximable mappings of Definition 2.1 and whose neighbourhoods are finite non-empty intersections of sets of the form

$$
[X, Y] = \{f : D_0 \to D_1 \mid X f Y\},
$$

where $X \in D_0$ and $Y \in D_1$. $\square$

We have been calling our mappings "approximable" for a long time now without saying exactly how they can be approximated! Definition 3.8 supplies the missing key, because once a domain has been defined, then the general theory gives an explicit meaning to the word approximation. We still have to verify, however, that the mappings do correspond to the elements of the domain.
**PROPOSITION 3.9.** Let neighbourhoods $X_i \in D_0$ and $Y_i \in D_1$ be given for $i < n$. Then the set of $[X_i, Y_i]$ for $i < n$ is consistent in $(D_0 \to D_1)$ iff the following condition holds:

(i) whenever $I \subseteq \{0, 1, \ldots, n-1\}$ and $\{X_i \mid i \in I\}$ is consistent in $D_0$, then $\{Y_i \mid i \in I\}$ must be consistent in $D_1$.

Moreover, when consistency holds, the least approximable mapping $f_0$ belonging to the intersection of the $[X_i, Y_i]$ is defined by:

(ii) $X f_0 Y$ iff $\bigcap \{Y_i \mid X \subseteq X_i\} \subseteq Y$ for $X \in D_0$ and $Y \in D_1$.

*Proof:* Suppose the $[X_i, Y_i]$ are consistent in $(D_0 \to D_1)$. Since the function space is being defined outright as a positive system, consistency means

$$
f \in \bigcap \{[X_i, Y_i] \mid i < n\}
$$

for some $f : D_0 \to D_1$. Now, with $f$ in hand, let us check condition (i). Suppose $\{X_i \mid i \in I\}$ is consistent. This means

$$
x \in \bigcap \{[X_i] \mid i \in I\}
$$

for some $x \in |D_0|$. Suppose $i \in I$, so $x \in [X_i]$. Since $X_i f Y_i$ holds, $f(x) \in [Y_i]$. This means, therefore, that

$$
f(x) \in \bigcap \{[Y_i] \mid i \in I\},
$$

and so $\{Y_i \mid i \in I\}$ is consistent.

For the converse, suppose (i) is the case. We take (ii) as the definition of a mapping and remark that for an arbitrary $X \in D_0$, the set $\{X_i \mid X \subseteq X_i\}$ is automatically consistent in $D_0$. By our assumption, the set $\{Y_i \mid X \subseteq X_i\}$ is therefore consistent. This means that

$$
\bigcap \{Y_i \mid X \subseteq X_i\} \in D_1.
$$

(Keep in mind that $i$ is restricted to those $i < n$, and there are only finitely many neighbourhoods being considered here.) It is thus almost immediate that the relation $f_0$ defined by (ii) satisfies conditions of 2.1 and so is an approximable mapping $f_0 : D_0 \to D_1$. By construction

$$
X_i f_0 Y_i
$$
holds trivially for all $i < n$; therefore,

$$
f_0 \in \bigcap \{[X_i, Y_i] \mid i < n\}
$$

and the desired consistency is established.

Finally suppose that $f$ is any mapping in the neighbourhood under discussion; this means $X_i f Y_i$ holds for all $i < n$. Suppose $X f_0 Y$ holds. We have for $X \subseteq X_i$, $X f Y_i$; so

$$
X f \bigcap \{Y_i \mid X \subseteq X_i\} \subseteq Y.
$$

Thus, $X f Y$ follows; hence, as relations, $f_0 \subseteq f$. In other words $f_0$ is the minimal element of the neighbourhood. $\square$

We note that, as a consequence of what we have just proved, when the neighbourhood is consistent, then

$$
\bigcap \{[X_i, Y_i] \mid i < n\} \subseteq [X, Y]
$$

is exactly equivalent to

$$
\bigcap \{Y_i \mid X \subseteq X_i\} \subseteq Y.
$$

Note also that a single neighbourhood $[X_0, Y_0]$ is always consistent since it contains the *constant mapping* $k$ where

$$
X k Y \text{ iff } Y_0 \subseteq Y,
$$

for all $X \in \mathcal{D}_0$ and $Y \in \mathcal{D}_1$. Some other simple observations about these neighbourhoods are just translations of the conditions of Definition 2.1:

$$
[\Delta_0, \Delta_1] = |\mathcal{D}_0 \to \mathcal{D}_1|;
$$

$$
[X, Y] \cap [X, Y'] = [X, Y \cap Y']; \text{ and}
$$

$$
X' \subseteq X \text{ and } Y \subseteq Y' \text{ imply } [X, Y] \subseteq [X', Y'],
$$

for all $X, X' \in \mathcal{D}_0$ and $Y, Y' \in \mathcal{D}_1$. We are now ready to prove the main result about the construct.

**THEOREM 3.10.** Given neighbourhood systems $\mathcal{D}_0$ and $\mathcal{D}_1$, the function space system $(\mathcal{D}_0 \to \mathcal{D}_1)$ is complete in the sense that every filter in $|\mathcal{D}_0 \to \mathcal{D}_1|$ is fixed by a unique approximable mapping.

*Proof:* Let $f : \mathcal{D}_0 \to \mathcal{D}_1$ be an approximable mapping. By the very definition of $(\mathcal{D}_0 \to \mathcal{D}_1)$ it determines a filter by the definition:
$$\hat{f} = \{ F \in (D_0 \to D_1) \mid f \in F \}.$$

Trivially $[X, Y] \in \hat{f}$ iff $f \in [X, Y]$ iff $X f Y$; so this filter uniquely determines the relation $f$. What we have to show is that every filter in $|D_0 \to D_1|$ is of this form.

Suppose $\varphi \in |D_0 \to D_1|$ is any filter. A relation can be defined at once by

$$X \hat{\varphi} Y \quad \text{iff} \quad [X, Y] \in \varphi.$$

In view of the remarks we made just before stating this theorem, there is no problem in showing that $\hat{\varphi}$ is an approximable mapping. Since the neighbourhoods of the function space are in any case finite intersections of sets like $[X, Y]$, those $[X, Y] \in \varphi$ generate $\varphi$. This means that $\hat{\hat{\varphi}} = \varphi$. By definition $\hat{\hat{f}} = f$, so there is a one-one correspondence between mappings and filters. (This correspondence is obviously inclusion preserving, too.) $\square$

We now know just about everything about $|D_0 \to D_1|$ as a domain: the elements correspond isomorphically to the approximable mappings; the finite elements are explained completely by 3.9; and we have seen how to calculate with neighbourhoods. The final step is to relate the function space to other domains by appropriate mappings. In doing this we shall freely construe elements of $|D_0 \to D_1|$ as approximable mappings in view of 3.10.

**THEOREM 3.11.** Given neighbourhood systems $D_1$ and $D_2$, there is a uniquely determined approximable mapping

$$\text{eval} : (D_1 \to D_2) \times D_1 \to D_2,$$

where for all $f : D_1 \to D_2$ and all $x \in |D_1|$ we have

(i) $\text{eval}(f, x) = f(x)$.

*Proof:* For $F \in (D_1 \to D_2)$ and $X \in D_1$ and $Y \in D_2$ define $\text{eval}$ as a relation by:

$$F, X \text{ eval } Y \quad \text{iff} \quad X f Y \text{ for all } f \in F.$$
Remember that neighbourhoods in the function space are sets of approximable mappings. It is easily checked that this definition makes eval approximable. We now calculate the function values by the formula of 2.2 (i):

$$
\text{eval}(f, x) = \{Y \in D_2 \mid \exists F \in (D_1 \to D_2)\ \exists X \in x.\ f \in F \text{ and } F \cup X \text{ eval } Y\}
$$

Because, again by 2.2 (i), we have

$$
f(x) = \{Y \in D_2 \mid \exists X \in x.\ X f Y\},
$$

we can see from the definition of eval that $\text{eval}(f, x) \subseteq f(x)$. Suppose that $Y \in f(x)$. Then $X f Y$ holds for some $X \in x$. We can write $f \in [X, Y] \in (D_1 \to D_2)$ and it is clear that

$$
[X, Y] \cup X \text{ eval } Y
$$

holds by definition. Therefore, $Y \in \text{eval}(f, x)$, and so $f(x) \subseteq \text{eval}(f, x)$. $\square$

This theorem is essential for our programme: it shows that in taking functions as objects the very basic operation of forming the function value is an approximable mapping. In other words we can treat the expression $f(x)$ not just as a function of $x$, as we have done from the start, but also as a function of $f$ as well. The result also indicates that there are useful maps defined on domains that themselves are function spaces; we shall meet many more of these. The next theorem provides further examples.

**THEOREM 3.12.** Given neighbourhood systems $D_0$, $D_1$, $D_2$ there is associated with every approximable mapping $g : D_0 \times D_1 \to D_2$ a uniquely determined approximable mapping

$$
\text{curry}(g) : D_0 \to (D_1 \to D_2)
$$

such that for $x \in |D_0|$ and $y \in |D_1|$

(i) $\text{curry}(g)(x)(y) = g(x, y)$.

Moreover we have these functional equations:

(ii) $\text{eval} \circ \langle \text{curry}(g) \circ p_0,\ p_1 \rangle = g$, and

(iii) $\text{curry}(\text{eval} \circ \langle h \circ p_0,\ p_1 \rangle) = h$,
where the $p_i : \mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}_i$ are the projection mappings and $h : \mathcal{D}_0 \to (\mathcal{D}_1 \to \mathcal{D}_2)$ is any approximable mapping. This provides an isomorphism between the domains $|\mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}_2|$ and $|\mathcal{D}_0 \to (\mathcal{D}_1 \to \mathcal{D}_2)|$ and so we can regard

$$\mathrm{curry} : (\mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}_2) \to (\mathcal{D}_0 \to (\mathcal{D}_1 \to \mathcal{D}_2))$$

as itself being an approximable mapping.

*Proof:* Given $g$ as indicated, we can define $\mathrm{curry}(g)$ as a relation and as an approximable mapping by:

$$X\ \mathrm{curry}(g)\ [Y, Z]\ \text{iff}\ X \cup Y\ g\ Z \quad \text{(but see Ex. 3.21)}$$

for all $X \in \mathcal{D}_0$, $Y \in \mathcal{D}_1$, $Z \in \mathcal{D}_2$. This is sufficient because an approximable mapping is intersective in the right-hand neighbourhood, so we know from the above exactly what $X\ \mathrm{curry}(g)\ \bigcap \{[Y_i, Z_i] \mid i < n\}$ means for all finite intersections. The remark after 3.9 is then helpful in checking that by this definition $\mathrm{curry}(g)$ satisfies the monotonicity condition and so is indeed approximable. We now calculate:

$$\begin{aligned}
\mathrm{curry}(g)(x)(y) &= \{Z \in \mathcal{D}_2 \mid \exists Y \in y.\ Y\ \mathrm{curry}(g)\ (x)\ Z\} \\
&= \{Z \in \mathcal{D}_2 \mid \exists Y \in y\ \exists X \in x.\ X\ \mathrm{curry}(g)\ [Y, Z]\} \\
&= \{Z \in \mathcal{D}_2 \mid \exists Y \in y\ \exists X \in x.\ X \cup Y\ g\ Z\} \\
&= \{Z \in \mathcal{D}_2 \mid \exists W \in \langle x, y \rangle.\ W\ g\ Z\} \\
&= g(\langle x, y \rangle) = g(x, y).
\end{aligned}$$

This proves (i). We also see, that if we take the left-hand side of (ii) and apply it to a pair $\langle x, y \rangle$, it reduces to $g(x, y)$ by virtue of (i). Thus, the two functions in (ii) are the same.

Turning to (iii), call the left-hand side $k$. Using (i) again, we find

$$\begin{aligned}
k(x)(y) &= \mathrm{eval} \circ \langle h \circ p_0, p_1 \rangle(\langle x, y \rangle) \\
&= \mathrm{eval}(\langle h \circ p_0(\langle x, y \rangle), p_1(\langle x, y \rangle) \rangle) \\
&= \mathrm{eval}(\langle h(x), y \rangle) \\
&= h(x)(y).
\end{aligned}$$

As this is true for all $y \in |\mathcal{D}_1|$, then $k(x) = h(x)$ follows. As this is true for all $x \in |\mathcal{D}_0|$, then $k = h$ follows, and (iii) is proved.
Taking (ii) and (iii) together, it is clear that the domains $|D_0 \times D_1 \to D_2|$ and $|D_0 \to (D_1 \to D_2)|$ are in a one-one correspondence.

$$
\text{curry}(g) \sqsubseteq \text{curry}(g') \text{ iff } g \sqsubseteq g'.
$$

Hence, curry is an isomorphism, and we can invoke 2.7 to conclude that it comes from an approximable mapping. $\square$

We close this lecture with some order-theoretic properties of function spaces that characterize inclusion and upper bounds of functions in a "pointwise" manner.

**THEOREM 3.13.** For approximable functions $f, g : D_0 \to D_1$ we have

(i) $f \sqsubseteq g$ iff $f(x) \sqsubseteq g(x)$ for all $x \in |D_0|$.

For subsets $F \subseteq |D_0 \to D_1|$ we have

(ii) $F$ is bounded in $|D_0 \to D_1|$ iff $\{f(x) \mid f \in F\}$ is bounded in $|D_1|$ for each $x \in |D_0|$;

and in that case for all $x \in |D_0|$:

(iii) $(\bigsqcup F)(x) = \bigsqcup \{f(x) \mid f \in F\}$.

*Proof.* The implication in (i) from left to right follows because evaluation is monotone in the function as well as the argument. The converse implication is a consequence of 2.2(ii).

For the proof of (ii) and (iii) we see that by (i) if $F$ is bounded, so is every set $\{f(x) \mid f \in F\}$. For the converse direction, it is clear that (iii) defines *some* pointwise mapping; we have only to prove that it is *approximable*. The calculation that $\sqcup F$ preserves directed unions (see 2.9 and 2.11) is probably the simplest way to reach the conclusion. $\square$
## EXERCISES

**EXERCISE 3.14.** For the most part we can assume that there is at most a countable number of tokens; thus, without loss of generality the underlying sets $\Delta_i$ of given systems $\mathcal{D}_i$ could be assumed to be subsets of $\Sigma^*$ where $\Sigma = \{0, 1\}$. (Any denumerable set would do.) Show that the product $\mathcal{D}_0 \times \mathcal{D}_1$ could be defined as the system over the set $0\Delta_0 \cup 1\Delta_1$ where

$$
\mathcal{D}_0 \times \mathcal{D}_1 = \{0X \cup 1Y \mid X \in \mathcal{D}_0 \text{ and } Y \in \mathcal{D}_1\}.
$$

In other words, the assumption of the disjointness of $\Delta_0$ and $\Delta_1$ is unnecessary. Give, therefore, the revised definition of $\langle x, y \rangle$ for elements, and prove that for a single system $\mathcal{D}$, there exists an approximable mapping

$$
\mathrm{diag} : \mathcal{D} \to \mathcal{D} \times \mathcal{D}
$$

where $\mathrm{diag}(x) = \langle x, x \rangle$ for all $x \in |\mathcal{D}|$. Also extend the definition to a product of $n$-factors

$$
\mathcal{D}_0 \times \mathcal{D}_1 \times \cdots \times \mathcal{D}_{n-1}
$$

which will be a system over the set

$$
\bigcup_{i < n} 1^i 0 \Delta_i.
$$

Note that for a 2-termed product we simplify $10\Delta_1$ to $1\Delta_1$.

**EXERCISE 3.15.** Establish the usual isomorphisms:

(i) $\mathcal{D}_0 \times \mathcal{D}_1 \cong \mathcal{D}_1 \times \mathcal{D}_0$;

(ii) $\mathcal{D}_0 \times (\mathcal{D}_1 \times \mathcal{D}_2) \cong (\mathcal{D}_0 \times \mathcal{D}_1) \times \mathcal{D}_2 \cong \mathcal{D}_0 \times \mathcal{D}_1 \times \mathcal{D}_2$.

How does the product of no factors fit in? Prove also:

(iii) $\mathcal{D}_0 \cong \mathcal{D}'_0$ and $\mathcal{D}_1 \cong \mathcal{D}'_1$ imply $\mathcal{D}_0 \times \mathcal{D}_1 \cong \mathcal{D}'_0 \times \mathcal{D}'_1$.
**EXERCISE 3.16.** Let $\mathcal{D}$ be a given neighbourhood system over $\Delta \subseteq \Sigma^*$. Define

$$
\Delta^\infty = \bigcup_{n=0}^\infty 1^n 0 \Delta,
$$

so that $\Delta^\infty$ is split into infinitely many disjoint copies of $\Delta$. Let $\mathcal{D}^\infty$ be the least family of subsets of $\Sigma^*$ where

1. $\Delta^\infty \in \mathcal{D}^\infty$, and
2. whenever $X \in \mathcal{D}$ and $Y \in \mathcal{D}^\infty$, then $0X \cup 1Y \in \mathcal{D}^\infty$.

Show that $\mathcal{D}^\infty$ is a neighbourhood system over $\Delta^\infty$. Prove the isomorphism

$$
\mathcal{D}^\infty \cong \mathcal{D} \times \mathcal{D}^\infty.
$$

Show, moreover, that the elements of $|\mathcal{D}^\infty|$ are in a one-one correspondence with arbitrary infinite sequences $\langle x_n \rangle_{n=0}^\infty$ of elements $x_n \in |\mathcal{D}|$ by using combinations of neighbourhoods

$$
0X_0 \cup 10X_1 \cup \cdots \cup 1^n 0X_n \cup \cdots,
$$

where from some point on all the $X_m$ are equal to $\Delta$.

**EXERCISE 3.17.** Using the $\mathcal{B}$ and $\mathcal{T}$ of Example 2.3 show there is a one-one approximable mapping

$$
f : \mathcal{B} \to \mathcal{T}^\infty
$$

and another approximable mapping

$$
g : \mathcal{T}^\infty \to \mathcal{B}
$$

such that

$$
g \circ f = I_{\mathcal{B}} \quad \text{and} \quad f \circ g \subseteq I_{\mathcal{T}^\infty}.
$$

Are $\mathcal{B}$ and $\mathcal{T}^\infty$ isomorphic? Are $\mathcal{B}$ and $\mathcal{T} \times \mathcal{B}$ isomorphic?
**EXERCISE 3.18.** Let $\mathcal{D}_0$ and $\mathcal{D}_1$ be neighbourhood systems over $\Delta_0$ and $\Delta_1$, where we again assume that these are subsets of $\Sigma^*$. We assume that in addition *no neighbourhood is empty*. Why is this possible without loss of generality?

Define the *sum system* by:

$$
\mathcal{D}_0 + \mathcal{D}_1 = \{\{\Lambda\} \cup 0\Delta_0 \cup 1\Delta_1\} \cup \{0X \mid X \in \mathcal{D}_0\} \cup \{1Y \mid Y \in \mathcal{D}_1\}.
$$

Prove that this is a neighbourhood system over $\{\Lambda\} \cup 0\Delta_0 \cup 1\Delta_1$. (Throwing in $\{\Lambda\}$ was not all that necessary, but note that $\mathcal{B} = \mathcal{B} + \mathcal{B}$, and this is an equality of sets not just an isomorphism of systems.)

Prove that in general there are mappings

$$
in_i : \mathcal{D}_i \to \mathcal{D}_0 + \mathcal{D}_1 \quad \text{and} \quad out_i : \mathcal{D}_0 + \mathcal{D}_1 \to \mathcal{D}_i,
$$

where $out_i \circ in_i = I_{\mathcal{D}_i}$. Where does the assumption $\emptyset \notin \mathcal{D}_i$ come in? How can these sums be generalized to $n$-terms? (Hint: As for products use sets $1^i 0 \Delta_i$.) Draw some pictures.

**EXERCISE 3.19.** Suppose we are given systems and approximable mappings

$$
f : \mathcal{D}_0 \to \mathcal{D}'_0 \quad \text{and} \quad g : \mathcal{D}_1 \to \mathcal{D}'_1.
$$

Prove there are approximable mappings

$$
f \times g : \mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}'_0 \times \mathcal{D}'_1 \quad \text{and} \quad f + g : \mathcal{D}_0 + \mathcal{D}_1 \to \mathcal{D}'_0 + \mathcal{D}'_1
$$

such that

(i) $(f \times g)(x, y) = \langle f(x), g(y) \rangle$ for all $x \in |\mathcal{D}_0|$ and $y \in |\mathcal{D}_1|$, and rewrite this as:

(ii) $f \times g = \langle f \circ p_0, g \circ p_1 \rangle$.

In addition prove that

(iii) $out_0 \circ (f + g) \circ in_0 = f$, and

(iv) $out_1 \circ (f + g) \circ in_1 = g$.

Do equations (iii) and (iv) uniquely determine $f + g$?
**EXERCISE 3.20.** (For category theorists). Show that the result of 3.19 can be used to prove that $\mathbf{+}$ and $\mathbf{\times}$ on the category of domains and approximable maps are indeed functors. Show further that $\mathbf{\times}$ is the categorical product for this category.

**EXERCISE 3.21.** In the proofs of 3.12 in the definition of curry ($g$) it is rather cavalierly assumed that the neighbourhood $[Y, Z]$ uniquely determines $Y$ and $Z$. Show that this is true if $Z \neq \Delta_2$. (Hint: Find explicitly the least of $f \in [Y, Z]$.) Show that if $Z = \Delta_2$ the biconditional stated at the start of the proof is still valid even though $Y$ is not uniquely determined. (Hint: Remember that $\Delta_1\ g\ \Delta_2$ must hold.) For arbitrary pairs of neighbourhoods of $(D_1 \to D_2)$ is there a simple criterion for identity?

**EXERCISE 3.22.** Prove that there is an approximable mapping

$$
\text{comp} : (D_1 \to D_2) \times (D_0 \to D_1) \to (D_0 \to D_2)
$$

where for all $g : D_1 \to D_2$ and $f : D_0 \to D_1$ we have

$$
\text{comp}(g, f) = g \circ f.
$$

Show this directly by writing down the neighbourhood relation and by building the mapping up from eval and curry (on suitable domains) using $\circ$ and $\langle,\,\rangle$. (Hint: Fill in maps in the following sequence of domains:

1. $(D_0 \to D_1) \times D_0 \to D_1$
2. $(D_1 \to D_2) \times ((D_0 \to D_1) \times D_0) \to (D_1 \to D_2) \times D_1$
3. $((D_1 \to D_2) \times (D_0 \to D_1)) \times D_0 \to (D_1 \to D_2) \times D_1$
4. $((D_1 \to D_2) \times (D_0 \to D_1)) \times D_0 \to D_2$
5. $(D_1 \to D_2) \times (D_0 \to D_1) \to (D_0 \to D_2)$.

The maps are of course not uniquely determined, but the shifting of brackets ought to suggest the right choice.)
**EXERCISE 3.23.** (For category theorists.) Show that the results of 3.11 and 3.12 prove that the category of domains and approximable mappings is a *cartesian closed category*. (Mac Lane [1971] pp. 95–96 may be consulted for a very brief introduction.) What is the *terminal domain* in this category? What sort of functor is $(D_0 \to D_1)$?

**EXERCISE 3.24.** Establish some more isomorphisms :

(i) $(D_0 \to (D_1 \times D_2)) \cong (D_0 \to D_1) \times (D_0 \to D_2)$

(ii) $(D_0 \to D_1^\infty) \cong (D_0 \to D_1)^\infty$

(iii) $D_0 \times (D_1 + D_2) \cong (D_0 \times D_1) + (D_0 \times D_2)$

(iv) $(D_0 + D_1) \to D_2 \cong (D_0 \to D_2) \times (D_1 \to D_2)$ . . .

If some of the above are not true, perhaps at least some mapping relationships can be established.

**EXERCISE 3.25.** (For topologists.) Recall from Exercises 1.21 and 2.13 on how to regard a domain $|D|$ as a topological space. Using 3.10 show that the family of open subsets of $|D|$ is isomorphic to a domain.

**EXERCISE 3.26.** Show that for every domain $D$ there is an approximable mapping

$$\mathrm{cond} : T \times D \times D \to D,$$

called the *conditional operator*, satisfying

(i) $\mathrm{cond}(\mathrm{true}, x, y) = x$

(ii) $\mathrm{cond}(\mathrm{false}, x, y) = y$

(iii) $\mathrm{cond}(\bot, x, y) = \bot$ .

(Hint: Recalling that $T = \{\{0\}, \{1\}, \{0, 1\}\}$, define cond as a relation by

$$
\begin{aligned}
0C \cup 10X \cup 110Y\ \mathrm{cond}\ Z \quad\text{iff}\quad & 0 \in C \text{ and } X \subseteq Z \text{ or} \\
& 1 \in C \text{ and } Y \subseteq Z \text{ or} \\
& 0, 1 \in C \text{ and } \Delta \subseteq Z ,
\end{aligned}
$$
where $C \in T$ and $X \in D$ and $Y \in D$ and where we are using the construction of Exercise 3.14.) Find a similar operator in the domain

$$
T \times D_0 \times D_1 \to D_0 + D_1 .
$$

Show also there is an approximable mapping

$$
\mathrm{which} : D_0 + D_1 \to T
$$

such that for all $x \in |D_0 + D_1|$

$$
\mathrm{cond}(\mathrm{which}(x), \mathrm{in}_0(\mathrm{out}_0(x)), \mathrm{in}_1(\mathrm{out}_1(x))) = x .
$$

**EXERCISE 3.27.** (For set theorists.) Give another proof that the family of approximable mappings $f : D_0 \to D_1$ is isomorphic to a domain by employing the general argument of Exercise 2.22. How does this compare with the proof method of 3.9 and 3.10? Can the general remarks also be employed to show that

$$
\mathrm{eval} : (D_1 \to D_2) \times D_1 \to D_2
$$

is approximable without bringing in the neighbourhoods in such an explicit way? (Hint: Use 3.5 and the idea of Exercise 2.12.)

**EXERCISE 3.28.** In the function space $(D_0 \to D_1)$ let

$$
\bigcap \{ [X_i, Y_i] \mid i < n \}
$$

be a (non-empty) neighbourhood. In 3.9 the minimal element of this neighbourhood is characterized as a relation $f_0$. Show that as an elementwise mapping it can be defined by the formula

$$
f_0(x) = \bigsqcup \{ \uparrow Y_i \mid x \in [X_i] \} ,
$$

for $x \in |D_0|$. Try to draw a picture of $|D_0|$ with neighbourhoods $[X_i]$ and the corresponding values of the function $f_0$.

**Lean 4**

- [NeighbourhoodSystems/DomainConstructs/C.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/C.lean)
- [NeighbourhoodSystems/DomainConstructs/C_dir.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/C_dir.lean)
- [NeighbourhoodSystems/DomainConstructs/C_inter.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/C_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/C_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/C_nonempty.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise314.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise314.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise314/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise314/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise314/diag.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise314/diag.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise314/proju2080_comp_diag.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise314/proju2080_comp_diag.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise314/proju2081_comp_diag.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise314/proju2081_comp_diag.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/BasicInst12.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/BasicInst12.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/Isomorphicu2eprod.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/Isomorphicu2eprod.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/prodAssocD.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/prodAssocD.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/prodCommD.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/prodCommD.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/prodCongrD.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/prodCongrD.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/prodCongrOrderIso.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/prodCongrOrderIso.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/prodUniqueOrderIso.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/prodUniqueOrderIso.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/prodUnitD.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/prodUnitD.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/prod_assoc_isomorphic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/prod_assoc_isomorphic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/prod_comm_isomorphic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/prod_comm_isomorphic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/prod_unit_isomorphic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/prod_unit_isomorphic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/uniqueProdOrderIso.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/uniqueProdOrderIso.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/unitProdD.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/unitProdD.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/unitSys.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/unitSys.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/unitSys_element_eq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/unitSys_element_eq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise315/unit_prod_isomorphic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise315/unit_prod_isomorphic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/component.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/component.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/component_ofSeq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/component_ofSeq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/eq_of_fiber_eq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/eq_of_fiber_eq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/fiber.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_inter.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_iterSys_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_iterSys_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_mono.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_single_ne.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_single_ne.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_single_self.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_single_self.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/interUpTo_subset_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/interUpTo_subset_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/iterProdIso.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/iterProdIso.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/iterSeqEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/iterSeqEquiv.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/iterSys.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/iterSys.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/iterSys_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/iterSys_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/iter_isomorphic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/iter_isomorphic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/le_of_component_le.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/le_of_component_le.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/mem_component.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/mem_component.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/mem_fiber.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/mem_fiber.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/mem_iterSys.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/mem_iterSys.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/mem_ofSeq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/mem_ofSeq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/natShiftEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/natShiftEquiv.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/ofSeq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/ofSeq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/ofSeq_component.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/ofSeq_component.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/ofSeq_mono.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/ofSeq_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/projN.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/projN.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/reconstruct_subset.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/reconstruct_subset.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/single.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/single.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/single_inter.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/single_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/single_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/single_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/single_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/single_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/single_mono.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/single_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/subset_single.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise316/subset_single.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/T.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/T.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/T_nbhd_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/T_nbhd_nonempty.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/Token.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/Token.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/bitNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/bitNbhd.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/bitNbhd_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/bitNbhd_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/comparable_of_agree.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/comparable_of_agree.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/encSet.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/encSet.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_agree.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_agree.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_anti.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_anti.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_nil.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/encSet_nil.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/exists_not_mem_bitNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/exists_not_mem_bitNbhd.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/f.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/f.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/f_injective.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/f_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/fg_le_id.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/fg_le_id.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/fiber_encSet_none.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/fiber_encSet_none.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/fiber_encSet_some.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/fiber_encSet_some.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/g.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/g.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/gf_eq_id.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/gf_eq_id.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/mem_encSet.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/mem_encSet.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise317/prefix_of_encSet_subset.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise317/prefix_of_encSet_subset.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/il.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/il.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/il_injective.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/il_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/il_mem_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/il_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/il_mem_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/il_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/il_preimage_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/il_preimage_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inMap₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inMap₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inMap₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inMap₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inju2080_injective.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inju2080_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inju2081_injective.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inju2081_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_inter.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_inter_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_inter_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_nonempty.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_subset_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_subset_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_subset_sumMaster.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_subset_sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_inter.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_nonempty.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_subset_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_subset_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_subset_sumMaster.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_subset_sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/ir.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/ir.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/ir_injective.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/ir_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/ir_mem_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/ir_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/ir_mem_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/ir_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/ir_preimage_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/ir_preimage_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_mono.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_sumMaster.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/mem_leftPart.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/mem_leftPart.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/mem_rightPart.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/mem_rightPart.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/none_mem_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/none_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/none_mem_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/none_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/none_mem_sumMaster.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/none_mem_sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/outMapu2080_comp_inMapu2080.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/outMapu2080_comp_inMapu2080.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/outMapu2081_comp_inMapu2081.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/outMapu2081_comp_inMapu2081.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/outMap₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/outMap₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/outMap₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/outMap₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_mono.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_sumMaster.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/sum.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/sum.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/sumMaster.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/sumMaster_inter_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/sumMaster_inter_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/sumMaster_inter_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise318/sumMaster_inter_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/paired_unique.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/paired_unique.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap_comp.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap_comp.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap_id.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap_id.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/proj_paired.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/proj_paired.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/toElementMap_prodMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/toElementMap_prodMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/toElementMap_prodMap_pair.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/toElementMap_prodMap_pair.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/eq_sumMaster_of_subset.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/eq_sumMaster_of_subset.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/mem_subset_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/mem_subset_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/mem_subset_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/mem_subset_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/not_inj₀_subset_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/not_inj₀_subset_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/not_inj₁_subset_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/not_inj₁_subset_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/outMapu2080_comp_sumMap_comp_inMapu2080.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/outMapu2080_comp_sumMap_comp_inMapu2080.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/outMapu2081_comp_sumMap_comp_inMapu2081.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/outMapu2081_comp_sumMap_comp_inMapu2081.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/sumMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/sumMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/interYs_single_not_subset_eq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/interYs_single_not_subset_eq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/interYs_single_subset_eq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/interYs_single_subset_eq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/leastStep.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/leastStep.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/leastStep_eq_of_step_eq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/leastStep_eq_of_step_eq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/leastStep_le.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/leastStep_le.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/leastStep_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/leastStep_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/leastStep_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/leastStep_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/stepCons.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/stepCons.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/step_eq_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/step_eq_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/step_eq_of_ne_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/step_eq_of_ne_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/step_eq_univ_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/step_eq_univ_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise321/step_master_right.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise321/step_master_right.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise322.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise322/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/compApp.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise322/compApp.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/compMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise322/compMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/toApproxMap_compMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise322/toApproxMap_compMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/toElementMap_compApp.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise322/toElementMap_compApp.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/toElementMap_compMap_apply.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise322/toElementMap_compMap_apply.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise323.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise323.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise323/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise323/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise323/BasicInst4.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise323/BasicInst4.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise323/BasicInst5.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise323/BasicInst5.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise323/homAdjunction.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise323/homAdjunction.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise323/toUnit.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise323/toUnit.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise323/toUnit_unique.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise323/toUnit_unique.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324/funProdEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324/funProdEquiv.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324/funProdIso.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324/funProdIso.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324/funProd_isomorphic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324/funProd_isomorphic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Distrib.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Distrib.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copair.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copair.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copairProj.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copairProj.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copairProj_copair.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copairProj_copair.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copair_comp_inMapu2080.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copair_comp_inMapu2080.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copair_comp_inMapu2081.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copair_comp_inMapu2081.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copair_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/copair_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/distribMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/distribMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/prod_mem_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Distrib/prod_mem_nonempty.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter/exists_forall_swap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter/exists_forall_swap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter/funIterEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter/funIterEquiv.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter/funIterIso.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter/funIterIso.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter/funIter_isomorphic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter/funIter_isomorphic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter/le_of_projComp_le.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter/le_of_projComp_le.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter/mapOfSeq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter/mapOfSeq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter/piCongrOrderIso.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter/piCongrOrderIso.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter/projComp_mono.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter/projComp_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise324Iter/toElementMap_mapOfSeq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise324Iter/toElementMap_mapOfSeq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise325.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise325.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/TD.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/TD.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/Tmem_eq_one.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/Tmem_eq_one.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/Tmem_eq_zero.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/Tmem_eq_zero.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/cond.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard_one.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard_one.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard_zero.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard_zero.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond_bot.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/cond_bot.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond_components.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/cond_components.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond_false.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/cond_false.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond_toElementMap_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/cond_toElementMap_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond_true.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/cond_true.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/one_ne_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/one_ne_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/zero_ne_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/zero_ne_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/zero_ne_one.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326/zero_ne_one.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Tmem_ge_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Tmem_ge_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Tmem_ge_one.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Tmem_ge_one.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Tmem_ge_zero.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Tmem_ge_zero.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSumEmb.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSumEmb.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSumEmb_toElementMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSumEmb_toElementMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum_bot.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum_bot.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum_false.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum_false.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum_true.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum_true.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/cond_which.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/cond_which.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inMapu2080_outMapu2080_eq_of_left.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inMapu2080_outMapu2080_eq_of_left.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inMapu2081_outMapu2081_eq_of_right.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inMapu2081_outMapu2081_eq_of_right.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inter_in_oneset.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inter_in_oneset.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inter_in_zeroset.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inter_in_zeroset.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/not_sum_mem_empty.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/not_sum_mem_empty.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/sum_element_trichotomy.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/sum_element_trichotomy.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard_left.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard_left.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard_masterC.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard_masterC.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard_right.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard_right.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/which_mem_one.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/which_mem_one.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/which_mem_zero.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise326Sum/which_mem_zero.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise327.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise327.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise328.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise328/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/Elementu2emem_interYs_of.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise328/Elementu2emem_interYs_of.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/leastMapVals.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise328/leastMapVals.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/leastMapVals_bounded.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise328/leastMapVals_bounded.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/leastMap_toElementMap_le_of_ub.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise328/leastMap_toElementMap_le_of_ub.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/toElementMap_leastMap_eq_sSup.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise328/toElementMap_leastMap_eq_sSup.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/val_le_leastMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise328/val_le_leastMap_toElementMap.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/ApproximableMapu2ele_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/ApproximableMapu2ele_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/BasicInst3.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/BasicInst3.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/MapsBounded.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/MapsBounded.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/PointwiseBounded.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/PointwiseBounded.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/curry.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/curry.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/curryEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/curryEquiv.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/curry_eval_comp.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/curry_eval_comp.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/curry_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/curry_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/curry_uncurry.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/curry_uncurry.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/eval.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/eval.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/evalMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/evalMap.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/evalMap_apply.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/evalMap_apply.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/eval_comp_curry.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/eval_comp_curry.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpace.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpace.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpaceEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpaceEquiv.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpaceEquiv_apply.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpaceEquiv_apply.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpaceEquiv_symm_apply.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpaceEquiv_symm_apply.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpace_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpace_master.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpace_mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpace_mem_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpace_mem_inter.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpace_mem_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpace_mem_up_closed.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/funSpace_mem_up_closed.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/gSection.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/gSection.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/gSection_le.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/gSection_le.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/gSection_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/gSection_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs_antitone.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs_antitone.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs_cons.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs_cons.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs_nil.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs_nil.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs_subset_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs_subset_master.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs_subset_of_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/interYs_subset_of_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/le_iff_toElementMap_le.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/le_iff_toElementMap_le.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/le_sSupMaps.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/le_sSupMaps.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/leastMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/leastMap.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/leastMap_le.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/leastMap_le.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/leastMap_mem_stepFun.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/leastMap_mem_stepFun.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/leastMap_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/leastMap_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/mapsBounded_iff_pointwiseBounded.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/mapsBounded_iff_pointwiseBounded.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/mapsBounded_principal.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/mapsBounded_principal.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/mapsBounded_to_filters.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/mapsBounded_to_filters.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/mem_interYs.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/mem_interYs.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/mem_step.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/mem_step.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/mem_stepFun.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/mem_stepFun.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/mem_stepFun_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/mem_stepFun_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/mem_toFilter.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/mem_toFilter.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/prod_mem_inl.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/prod_mem_inl.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/prod_mem_inr.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/prod_mem_inr.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/rel_interYs.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/rel_interYs.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/rel_stepFun_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/rel_stepFun_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/sSupMaps.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/sSupMaps.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/sSupMaps_le.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/sSupMaps_le.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/step.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/step.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_append.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_append.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_cons.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_cons.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_nil.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_nil.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_singleton.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_subset_step_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_subset_step_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_up_closed.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/stepFun_up_closed.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/step_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/step_inter_right.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/step_master_eq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/step_master_eq.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/step_mem.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/step_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/step_subset.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/step_subset.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/supOnPrincipal.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/supOnPrincipal.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/supOnPrincipal_mono.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/supOnPrincipal_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/toApproxMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/toApproxMap.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/toApproxMap_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/toApproxMap_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/toElementMap_curry_apply.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/toElementMap_curry_apply.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/toElementMap_sSupMaps.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/toElementMap_sSupMaps.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/toElementMap_sSupMaps_principal.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/toElementMap_sSupMaps_principal.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/toElementMap_sSupMapsu27.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/toElementMap_sSupMapsu27.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/toElementMapu2082_eval.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/toElementMapu2082_eval.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/toFilter.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/toFilter.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/toFilter_le_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/toFilter_le_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/uncurry.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/uncurry.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/uncurry_curry.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/uncurry_curry.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/uncurry_eq.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/uncurry_eq.lean)
- [NeighbourhoodSystems/DomainConstructs/FunctionSpace/uncurry_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/FunctionSpace/uncurry_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/Product.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/ApproximableMapu2erel_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/ApproximableMapu2erel_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/constMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/constMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/constMap_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/constMap_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/ext.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/ext.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/fst.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/fst.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/fst_pair.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/fst_pair.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/inl_preimage_prodNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/inl_preimage_prodNbhd.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/inr_preimage_prodNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/inr_preimage_prodNbhd.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/map₂Equiv.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/map₂Equiv.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/mem_fst.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/mem_fst.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/mem_pair.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/mem_pair.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/mem_pair_prodNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/mem_pair_prodNbhd.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/mem_prodNbhd_inl.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/mem_prodNbhd_inl.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/mem_prodNbhd_inr.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/mem_prodNbhd_inr.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/mem_snd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/mem_snd.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/ofMap₂.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/ofMap₂.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/ofMap₂_toMap₂.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/ofMap₂_toMap₂.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/pair.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/pair.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/pair_fst_snd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/pair_fst_snd.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/pair_le_pair_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/pair_le_pair_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/paired.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/paired.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/paired_proj.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/paired_proj.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/paired_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/paired_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prod.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prod.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prodEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prodEquiv.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prodEquiv_apply.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prodEquiv_apply.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prodEquiv_symm_apply.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prodEquiv_symm_apply.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prodNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prodNbhd.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prodNbhd_injective.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prodNbhd_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prodNbhd_inter.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prodNbhd_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prodNbhd_preimage.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prodNbhd_preimage.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prodNbhd_subset_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prodNbhd_subset_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prod_master.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prod_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prod_mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prod_mem_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prod_mem_prodNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prod_mem_prodNbhd.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prod_mem_prodNbhd_iff.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prod_mem_prodNbhd_iff.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/prod_mem_split.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/prod_mem_split.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/proju2080_comp_paired.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/proju2080_comp_paired.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/proju2081_comp_paired.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/proju2081_comp_paired.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/proj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/proj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/proj₀_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/proj₀_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/proj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/proj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/proj₁_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/proj₁_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/snd.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/snd.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/snd_pair.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/snd_pair.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/substitution_toElementMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/substitution_toElementMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/toElementMap_constMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/toElementMap_constMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/toElementMap_paired.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/toElementMap_paired.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/toElementMap_proj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/toElementMap_proj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/toElementMap_proj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/toElementMap_proj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/toElementMapu2082_toMapu2082.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/toElementMapu2082_toMapu2082.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/toMap₂.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/toMap₂.lean)
- [NeighbourhoodSystems/DomainConstructs/Product/toMap₂_ofMap₂.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Product/toMap₂_ofMap₂.lean)
- [NeighbourhoodSystems/DomainConstructs/funSpaceReprIso.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/funSpaceReprIso.lean)
- [NeighbourhoodSystems/DomainConstructs/graph.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/graph.lean)
- [NeighbourhoodSystems/DomainConstructs/graphEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/graphEquiv.lean)
- [NeighbourhoodSystems/DomainConstructs/graph_injective.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/graph_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/joinMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/joinMap.lean)
- [NeighbourhoodSystems/DomainConstructs/mapOfOpen.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/mapOfOpen.lean)
- [NeighbourhoodSystems/DomainConstructs/mapOfOpen_rel.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/mapOfOpen_rel.lean)
- [NeighbourhoodSystems/DomainConstructs/mapOfOpen_rel_empty.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/mapOfOpen_rel_empty.lean)
- [NeighbourhoodSystems/DomainConstructs/meetMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/meetMap.lean)
- [NeighbourhoodSystems/DomainConstructs/mem_graph.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/mem_graph.lean)
- [NeighbourhoodSystems/DomainConstructs/openIso.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/openIso.lean)
- [NeighbourhoodSystems/DomainConstructs/openOfMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/openOfMap.lean)
- [NeighbourhoodSystems/DomainConstructs/openOfMap_isOpen.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/openOfMap_isOpen.lean)
- [NeighbourhoodSystems/DomainConstructs/opensReprIso.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/opensReprIso.lean)
- [NeighbourhoodSystems/DomainConstructs/sInter_eq_graph_meetMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/sInter_eq_graph_meetMap.lean)
- [NeighbourhoodSystems/DomainConstructs/sUnion_eq_graph_joinMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/sUnion_eq_graph_joinMap.lean)
- [NeighbourhoodSystems/DomainConstructs/sierpinski.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/sierpinski.lean)
