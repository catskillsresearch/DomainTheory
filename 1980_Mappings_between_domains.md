# Mappings between domains

The elements of a domain are regarded as being specified by approximations: the neighbourhoods. With the idea of approximation as the dominant notion, therefore, it is natural to look for a concept of mapping (transformation of domains) that in some suitable sense preserves the spirit of the approximations. In a 'theory of computability,' where the (finite) approximations to the elements are all we can ever know at one time, the only mappings that can be computed are those that proceed by approximation, somehow passing from the neighbourhoods of one domain over to the neighbourhoods of the other.

Suppose $X \in \mathcal{D}_0$ is given - it is an approximation to certain elements of $|\mathcal{D}_0|$. (More precisely $\uparrow X$ is the approximation in the domain, but it is easier to speak of the neighbourhood $X$.) What can be said about the approximations of the images of these elements under the mapping we will call $f$? If $X$ is not a very sharp approximation, then not very much can be said about the image in the other domain $|\mathcal{D}_1|$. Trivially, of course, we can say that $\Delta_1$ is an approximation - because it approximates everything in its domain. Suppose, however, that we could say more. Suppose we could say that both $Y$ and $Y'$ approximate the image of $X$. If the mapping $f$ is coherent, then it is reasonable to suppose that such a statement would imply that $Y$ and $Y'$ are *consistent* in $\mathcal{D}_1$. But if this is so, then since the two neighbourhoods are meant to cluster around the same images, we can feel some confidence in saying that $Y \cap Y'$ approximates these images. In other words to specify $f$ we do not supply a unique image of $X$, but we say which of the $Y \in \mathcal{D}_1$ approximate the (ideal) image. To make this idea work a *monotonicity condition* is also needed since we are trying to express the idea that "if we give at least $X$ as an approximate input to $f$, then we can expect at least $Y$ as output." Thus,
a mapping is taken as a kind of relation between neighbourhoods.

**DEFINITION 2.1.** An *approximable mapping* $f : D_0 \to D_1$ between domains is a binary relation $f \subseteq D_0 \times D_1$ between neighbourhoods such that

(i) $\Delta_0 f \Delta_1$ ;

(ii) $X f Y$ and $X f Y'$ always imply $X f (Y \cap Y')$ ;

(iii) $X f Y$, $X' \subseteq X$, and $Y \subseteq Y'$ always imply $X' f Y'$. $\square$

Condition (i) we have already discussed; in a sense it means “ask me no questions and I shall tell you no lies.” In other words “zero input can expect at least zero output.” The other conditions are compatible with having

$$
f = \{ \langle X, \Delta_1 \rangle \mid X \in D_0 \};
$$

that is, $f$ might be the least informative relation and nothing more. But if it is more, then (ii) is, as we explained, a consistency condition. To explain monotonicity in (iii), suppose a mapping relationship is already known, $X f Y$, say. If we *improve* the accuracy of $X$ to $X' \subseteq X$ and if we *degrade* the accuracy of $Y$ to $Y' \supseteq Y$, then we can still assert $X' f Y'$ since this relationship is *less informative* than the former relationship, which was already known. Thus, we see that conditions (i)–(iii) are all reasonably argued as necessary.

One indication that the conditions of 2.1 are sufficient for a definition is that they are exactly what we need to show that $f$ as a neighbourhood relation determines an equivalent elementwise mapping from $|D_0|$ into $|D_1|$. (Owing to the equivalence, we use the same symbol $f$ for both.)

**PROPOSITION 2.2.** Given neighbourhood systems $D_0$ and $D_1$, an approximable mapping $f : D_0 \to D_1$ always determines a function $f : |D_0| \to |D_1|$ between domains by virtue of the formula:

(i) $f(x) = \{ Y \in D_1 \mid \exists X \in x.\ X f Y \}$

for all $x \in |D_0|$. Conversely, this function uniquely determines
the original relation by the equivalence:

(ii) $X f Y$ iff $Y \in f(\uparrow X)$

for all $X \in D_0$ and $Y \in D_1$. Approximable functions are always monotone in the following sense:

(iii) $x \subseteq y$ always implies $f(x) \subseteq f(y)$,

for $x, y \in |D_0|$; moreover two approximable functions $f : D_0 \to D_1$ and $g : D_0 \to D_1$ are identical as relations iff

(iv) $f(x) = g(x)$, for all $x \in |D_0|$.

**Proof:** The argument that formula (i) always gives us $f(x) \in |D_1|$ when $x \in |D_0|$ can be safely left to the reader. Note, however, that all the conditions of 2.1 are required to show this. As for (ii), the implication from left to right follows directly from (i) because $X \in \uparrow X$. In the other direction $Y \in f(\uparrow X)$ means that $Z f Y$ holds for some $Z \in \uparrow X$. But from $X \subseteq Z$ it follows that $X f Y$, as we wished.

To prove monotonicity, assume $x \subseteq y$. Now $X \in x$ and $X f Y$ always imply $X \in y$ and $X f Y$. This means $Y \in f(x)$ always implies $Y \in f(y)$; that is, $f(x) \subseteq f(y)$.

Finally, to check that (iv) means $f = g$ as relations, all that has to be remarked that this follows from formulae (i) and (ii). $\square$

Note that the right-hand side of (ii) can be written:

$$\uparrow Y \subseteq f(\uparrow X),$$

which can be read as saying that the partial element determined by the neighbourhood $Y$ approximates the function value at the element determined by $X$. This precise relationship of course fits the informal discussion of mapping given earlier. Indeed whenever $x \in [X]$ and $X f Y$ hold, then $f(x) \in [Y]$ always follows, which is another way to construe the mapping character of $f$. Some examples of mappings are now called for.
**EXAMPLE 2.3.** Let $T$ be the neighbourhood system of the two-token domain of Example 1.2. To avoid confusion with some other domains, we will call the two total elements of $|T|$ respectively true and false. There is only one other finite element here, namely $\perp = \text{undefined}$. We often use these elements as indicators of results: true indicates a positive outcome; false, a negative outcome; and $\perp$ indicates that there is not enough information to decide the outcome totally.

Let $B$ be the system for the binary tree as in the last chapter. What we wish to define is an approximable mapping $f : B \to T$. The intuitive idea of the mapping we have in mind is that the binary sequence is being read from left to right, and we are counting the number of 0's seen before the first 1 is encountered. We then test the parity of this count; if it is even, the output is true; if not, false. Using a suggestive informal notation with three dots, some results of the function that does the counting and testing can be written as:

$$
\begin{aligned}
f(0000101\dots) &= \text{true} \\
f(1101110\dots) &= \text{true} \\
f(0111011\dots) &= \text{false} \\
f(0000000\dots) &= \perp.
\end{aligned}
$$

The last equation is necessary, because $0000000$ as a partial element cannot be counted as either even or odd since it can have inconsistent extensions:

$$
\begin{aligned}
0000000\,\perp &\sqsubseteq 00000001\,\perp \\
0000000\,\perp &\sqsubseteq 000000000001\,\perp.
\end{aligned}
$$

So, as far as $f$ is concerned, a plain string of 0's is indefinite. The same answer holds if the 0's go on infinitely.

To be more precise we want

$$
\begin{aligned}
f(0^n 1\,\perp) &= \text{true} && \text{if } n \text{ is even;} \\
&= \text{false} && \text{if } n \text{ is odd.}
\end{aligned}
$$

As a binary relation $f \subseteq B \times T$ we will have

$$
X f Y \text{ iff } Y \in \perp \text{ or } X \sqsubseteq 0^n 1 \Delta \text{ for some } n \in \mathbf{N} \text{ and either } n \text{ is even and } Y \in \text{true or } n \text{ is odd and } Y \in \text{false.}
$$

It should be checked that 2.1(i)–(ii) are satisfied. $\square$
**EXAMPLE 2.4.** Let us briefly describe an approximable mapping $g : B \to B$. Informally, $g$ can be said to "read a sequence from left to right and eliminate the first consecutive run of 1's while copying all the other digits as read." We will have

$$
g(0^n 1^k 0 x) = 0^{n+1} x
$$

provided $k > 0$. (Here $1^k$ means a string of 1's of length $k$.) However, if $1^\infty$ is the infinite sequences of 1's, then

$$
\begin{aligned}
g(1^\infty) &= \perp, \text{ and} \\
g(0^n 1^\infty) &= 0^n.
\end{aligned}
$$

This example is instructive, since it shows that a non-trivial mapping can transform a total element into a partial element. $\square$

Aside from our being able to define particular functions outright, we can combine functions in many different ways; the idea of composition is probably the most basic scheme of combination, and there is a technical name for a family of structures with mappings that can be so combined.

**THEOREM 2.5.** The class of neighbourhood systems and approximable mappings form a *category*, where the identity mapping $I_D : D \to D$ relates $X, Y \in D$ as follows:

(i) $X\ I_D\ Y$ iff $X \subseteq Y$.

If $f : D_0 \to D_1$ and $g : D_1 \to D_2$ are given, then the *composition* $g \circ f : D_0 \to D_2$ relates $X \in D_0$ and $Z \in D_2$ as follows:

(ii) $X\ g \circ f\ Z$ iff $\exists Y \in D_1.\ X\ f\ Y$ and $Y\ g\ Z$.

*Proof:* (We may use MacLane [1971] as the standard reference on category theory, but we require hardly more than the basic definitions at this stage.) To check that we have a category, we need to know that the identity and composition maps really are maps in the category and that certain identity and associative laws hold. Now it is obvious that $I_D$ satisfies 2.1 (i)-(iii). Moreover if $f : D_0 \to D_1$, all we have to prove is:
$$
f \circ I_{D_0} = I_{D_1} \circ f = f
$$

Checking one of these equations is enough. Thus, for $X \in D_0$ and $Z \in D_1$ we find

$$
\begin{aligned}
X\ f \circ I_{D_0}\ Z &\text{ iff } \exists Y \in D_0.\ X \subseteq Y \text{ and } Y\ f\ Z \\
&\text{ iff } X\ f\ Z.
\end{aligned}
$$

So, $f$ and $f \circ I_{D_0}$ are the same mapping.

Suppose now that $f : D_0 \to D_1$ and $g : D_1 \to D_2$. We have to verify that $g \circ f$ is an approximable mapping. First off, there is no trouble in seeing that $\Delta_0\ g \circ f\ \Delta_2$ holds. Next, suppose that $X\ g \circ f\ Z$ and $X\ g \circ f\ Z'$ hold. Then we have $X\ f\ Y$ and $Y\ g\ Z$ for some choice of $Y \in D_1$. Also $X\ f\ Y'$ and $Y'\ g\ Z'$ hold for some choice of $Y' \in D_1$. By 2.1 (ii) it follows that $X\ f\ (Y \cap Y')$. Since $Y \cap Y' \subseteq Y$, we conclude $(Y \cap Y')\ g\ Z$ by 2.1 (iii); similarly $(Y \cap Y')\ g\ Z'$. Invoking 2.1 (ii) again, we obtain $(Y \cap Y')\ g\ (Z \cap Z')$, and $X\ g \circ f\ (Z \cap Z')$ is proved.

Suppose finally that $X' \subseteq X$, $X\ g \circ f\ Z$, and $Z \subseteq Z'$. Now $X\ f\ Y$ and $Y\ g\ Z$ for some $Y \in D_1$. But then $X'\ f\ Y$ holds; for a similar reason $Y\ g\ Z'$ holds also. Therefore, $X'\ g \circ f\ Z'$ is established, which means that we have checked 2.1 (iii) for $g \circ f$ and have completed the proof that $g \circ f : D_0 \to D_2$.

The verification of associativity is a purely logical deduction. Thus suppose that in addition to $f$ and $g$ we have $h : D_2 \to D_3$. If $X \in D_0$ and $W \in D_3$ we find

$$
\begin{aligned}
X\ h \circ (g \circ f)\ W &\text{ iff } \exists Z \in D_2.\ X\ g \circ f\ Z \text{ and } Z\ h\ W \\
&\text{ iff } \exists Z \in D_2\ \exists Y \in D_1.\ X\ f\ Y \text{ and } Y\ g\ Z \text{ and } Z\ h\ W \\
&\text{ iff } \exists Y \in D_1\ \exists Z \in D_2.\ X\ f\ Y \text{ and } Y\ g\ Z \text{ and } Z\ h\ W \\
&\text{ iff } \exists Y \in D_1.\ X\ f\ Y \text{ and } Y\ (h \circ g)\ W \\
&\text{ iff } X\ (h \circ g) \circ f\ W.
\end{aligned}
$$

So, as relations, $h \circ (g \circ f) = (h \circ g) \circ f$. $\square$

It may seem as though we have, in the definition of composition, written things backwards. But the reason is that when mappings are taken as elementwise functions, then the order is preserved in expressions involving the usual function value notation. We have, for example:
**PROPOSITION 2.6.** Given $f : D_0 \to D_1$ and $g : D_1 \to D_2$, the following equations hold:

(i) $I_{D_0}(x) = x$, and

(ii) $(g \circ f)(x) = g(f(x))$,

for all $x \in |D_0|$. $\square$

The proof is not troublesome and is left as an exercise. In technical language the result shows that the category defined in Theorem 2.5 is equivalent to a "concrete category" of sets and functions, namely the domains and elementwise transformations of 2.2.

Toward the end of the last lecture (see 1.9) we promised to show that isomorphisms of domains always come from approximable mappings, and this we now do. It means that the category contains all the isomorphisms it should have.

**THEOREM 2.7.** Every isomorphism between domains results from an approximable mapping between the neighbourhood systems. Moreover, finite elements are always transformed into finite elements.

*Proof:* Suppose that $f : |D_0| \to |D_1|$ is a one-one, inclusion-preserving function defined on elements, where the range of the function is the whole of $|D_1|$, of course. Taking the hint from 2.2, there is only one way we could define a neighbourhood mapping; namely, we consider the relation $Y \in f(\uparrow X)$ for $X \in D_0$ and $Y \in D_1$. What has to be shown is that this is an approximable mapping which determines the original function via the formula 2.2 (i).

The first part is easy; indeed, there is a general result that monotone functions on finite elements of one domain to arbitrary elements of another domain always determine approximable mappings (cf. Exercise 2.8). What remains, then, is to show that the relation re-defines the function. This comes down to showing that for $x \in |D_0|$

$$
f(x) = \{ Y \in D_1 \mid \exists X \in x.\ Y \in f(\uparrow X) \}.
$$
Consider the right-hand side of this equation: it is a filter. (This either can be proved directly or Exercise 2.11 can be used.) Because $f$ is an onto-function, we can call the right-hand side $f(x')$ for some $x' \in |D_0|$. But since $X \in x$ implies $\uparrow X \subseteq x$ and $f(\uparrow X) \subseteq f(x)$, the right-hand side is included in the left-hand side. In other words $f(x') \subseteq f(x)$. But, since $f$ is an isomorphism, $x' \subseteq x$ follows.

In the other direction, if $X \in x$, then $f(\uparrow X) \subseteq f(x')$ holds by definition, so $\uparrow X \subseteq x'$. This implies $X \in x'$; and, as $X$ is arbitrary, $x \subseteq x'$. So $x = x'$, and $f(x) = f(x')$ as desired.

Finally, consider any finite element $\uparrow X \in |D_0|$, where $X \in D_0$. What we have to show is that $f(\uparrow X)$ is finite in $|D_1|$. Because $f$ is an isomorphism, we can associate uniquely to every $Y \in f(\uparrow X)$ an element $y_Y \subseteq \uparrow X$ in $|D_0|$ where $f(y_Y) = \uparrow Y$. (Just apply the inverse of the function $f$.) Define

$$
z = \bigcup \{ y_Y \mid Y \in f(\uparrow X) \}.
$$

Because $Y' \subseteq Y$ always implies $y_{Y'} \subseteq y_Y$ and each $y_Y \in |D_0|$, it is easy to show $z$ is a filter and hence is in $|D_0|$ also (cf. Exercise 2.11). Because each $y_Y \subseteq \uparrow X$, then $z \subseteq \uparrow X$, too. But each $y_Y \subseteq z$, so $\uparrow Y = f(y_Y) \subseteq f(z)$ and hence $Y \in f(z)$. As this holds for all $Y \in f(\uparrow X)$, the inclusion $f(\uparrow X) \subseteq f(z)$ follows, as well as $\uparrow X \subseteq z$. Therefore, $z = \uparrow X$ and so $X \in z$. But then $X \in y_Y$ for some $Y \in f(\uparrow X)$, by definition of $z$. Since $\uparrow X \subseteq y_Y$, we obtain $f(\uparrow X) \subseteq \uparrow Y$, but of course the opposite inclusion is also true from the choice of $Y$. This means that $f(\uparrow X) = \uparrow Y$ is finite in $|D_1|$ as claimed. We can apply the same argument to the inverse function; and, thus, the finite elements of $|D_0|$ and $|D_1|$ are in a one-one inclusion-preserving correspondence under the isomorphism. $\square$

## EXERCISES

**EXERCISE 2.8.** With reference to the proof of 2.2 show that an approximable mapping is uniquely determined by its elementwise effect on finite elements. Moreover any arbitrary monotone function on finite elements of $|D_0|$ with values in $|D_1|$ comes from an approximable $f : D_0 \to D_1$.
**EXERCISE 2.9.** Prove that if $f : D_0 \to D_1$ is an approximable mapping, then the elementwise mapping $f : |D_0| \to |D_1|$ satisfies the equation

$$
f(x) = \bigcup \{ f(\uparrow X) \mid X \in x \}
$$

for all $x \in |D_0|$. Conversely, show that every elementwise function satisfying this equation comes from an approximable mapping as defined in 2.2.

**EXERCISE 2.10.** Carry out the proof of Proposition 2.6; and in addition show that, if $f, g : D_0 \to D_1$ are two approximable mappings, there exists $h : D_0 \to D_1$ such that

$$
h(x) = f(x) \cap g(x)
$$

for all $x \in |D_0|$.

**EXERCISE 2.11.** Let $(I, \le)$ be a non-empty abstract partially ordered set; suppose it is <u>directed</u> in the sense that whenever $i, j \in I$, then $i \le k$ and $j \le k$ for some $k \in I$. Suppose that $a : I \to |D|$ is such that

$$
i \le j \text{ implies } a_i \subseteq a_j
$$

for all $i, j \in I$. Prove that

$$
\bigcup \{ a_i \mid i \in I \}
$$

is always a filter in $|D|$. (Note the ways this lemma could be used in the proof of 2.7; but be careful in defining the partially ordered set and do not confuse $\subseteq$ and $\supseteq$.) In words we could say that the domain of filters is <u>closed under directed unions</u>. Prove also that if $f : D \to D'$ is an approximable mapping, then for any directed union

$$
f(\bigcup \{ a_i \mid i \in I \}) = \bigcup \{ f(a_i) \mid i \in I \};
$$

that is, <u>approximable mappings always preserve directed unions</u>. If an elementwise function preserves directed unions, must it come from an approximable mapping? (Hint: Invoke 2.9.)
**EXERCISE 2.12.** Suppose $(I, \le)$ is a directed, partially ordered set and $f_i : D_0 \to D_1$ is a family of approximable mappings indexed by $i \in I$, where we assume

$$
i \le j \text{ implies } f_i(x) \subseteq f_j(x)
$$

for all $i, j \in I$ and all $x \in |D_0|$. Prove that there is an approximable mapping $g : D_0 \to D_1$ where

$$
g(x) = \bigcup \{ f_i(x) \mid i \in I \}
$$

for all $x \in |D_0|$.

**EXERCISE 2.13.** (For topologists.) Recall Exercise 1.22 where it was shown that any domain $|D|$ is a topological space. Prove from Exercise 2.9 that the functions $f : |D_0| \to |D_1|$ determined by approximable mappings are exactly *the continuous functions between these spaces.* (Hint: To prove continuity, remark that by 2.9

$$
f^{-1}[Y] = \bigcup \{ [X] \mid Y \in f(\uparrow X) \};
$$

hence, the inverse image of any open set is open. In the other direction, suppose that $f : |D_0| \to |D_1|$ is topologically continuous. Argue that for all $x \in |D_0|$ and all open subsets $U \subseteq |D_1|$ we have

$$
f(x) \in U \text{ iff } \exists X \in x.\ f(\uparrow X) \in U.
$$

This holds because an open subset of $|D_0|$ is always a union of basic open subsets of the form $[X']$ for $X \in D_0$ and because

$$
x = \bigcup \{ \uparrow X \mid X \in x \}
$$

for all $x \in |D_0|$.)

**EXERCISE 2.14.** Let $f : |D_0| \to |D_1|$ be an isomorphism between domains. Let $\varphi : D_0 \to D_1$ be the one-one correspondence between neighbourhoods provided by Theorem 2.7 where

$$
f(\uparrow X) = \uparrow \varphi(X)
$$

for all $X \in D_0$. Show that the approximable mapping determined by $f$ is just the relationship $\varphi(X) \subseteq Y$. In addition prove that if $X, X' \in D_0$ are consistent, then

$$
\varphi(X \cap X') = \varphi(X) \cap \varphi(X').
$$
Remark that the isomorphisms between domains correspond exactly to the isomorphisms between neighbourhood systems (in the sense of one-one inclusion preserving correspondences).

**EXERCISE 2.15.** (For topologists.) Consider the one-token system with

$$\mathcal{O} = \{ \{0\}, \emptyset \}.$$

We can regard $|\mathcal{O}|$ as having just two finite elements $\bot$ (bottom) and $\top$ (top), where $\bot \sqsubseteq \top$. For any system $D$, show that the open subsets $U$ of $|D|$ are in a one-one correspondence with the approximable mappings $f : D \to \mathcal{O}$, where the correspondence is given by the equation

$$U = \{ x \in |D| \mid f(x) = \top \}.$$

What are the open subsets of $|\mathcal{O}|$? of $|\mathbb{T}|$? of $|\mathbb{B}|$?

**EXERCISE 2.16.** In the discussion of $\mathbb{B}$ in Chapter 1 we defined a mapping $x \mapsto \sigma x$ for any given $\sigma \in \Sigma^*$. Is this (elementwise) mapping approximable? Show in addition that the mapping $f : \mathbb{B} \to \mathbb{T}$ of 2.3 is uniquely determined among approximable mappings by the equations:

$$f(1x) = \text{true},$$
$$f(01x) = \text{false, and}$$
$$f(00x) = f(x).$$

**EXERCISE 2.17.** Establish in detail that the mapping $g : \mathbb{B} \to \mathbb{B}$ of Exercise 2.4 is approximable. Is it uniquely determined by these equations:

$$g(0x) = 0g(x),$$
$$g(11x) = g(1x),$$
$$g(10x) = 0x,$$
$$g(1) = \bot,$$

or are some missing?
**EXERCISE 2.18.** What is the meaning in words of the approximable mapping $h : \mathbb{B} \to \mathbb{B}$, where

$$h(0x) = 00h(x), \text{ and}$$
$$h(1x) = 10h(x),$$

for all elements $x \in |\mathbb{B}|$? Is $h$ an isomorphism? Does there exist a map $k : \mathbb{B} \to \mathbb{B}$ where

$$k \circ h = I_{\mathbb{B}},$$

and is $k$ one-one?

**EXERCISE 2.19.** Generalize Definition 2.1 in an appropriate way in order to define the concept of *an approximable mapping*

$$f : \mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}_2$$

of two variables. (Hint: $f$ can be taken to be a certain kind of ternary relation

$$f \subseteq \mathcal{D}_0 \times \mathcal{D}_1 \times \mathcal{D}_2,$$

where we can write

$$X, Y\ f\ Z$$

for the relationship among neighbourhoods.) What is the corresponding version of Proposition 2.2 for functions of two variables?

**EXERCISE 2.20.** Discuss again the example of Exercise 1.15 where the domain turns out to be the powerset (set of all subsets) of $\mathbf{N}$. Show how the finite elements can be taken to be the finite subsets of $\mathbf{N}$ and can be identified with the tokens of a suitable neighbourhood system $\mathcal{P}$. (Hint: Define $\uparrow F$ for finite sets $F \subseteq \mathbf{N}$.) Show that both union and intersection ($x \cup y$ and $x \cap y$) are functions on $|\mathcal{P}|$ that are approximable in the sense of Exercise 2.19. (The elements of $|\mathcal{P}|$ are being identified with arbitrary sets $x \subseteq \mathbf{N}$.) Show also that the following transformations are approximable:

$$x + 1 = \{n + 1 \mid n \in x\}, \text{ and}$$
$$x - 1 = \{n \mid n + 1 \in x\}.$$
**EXERCISE 2.21.** The system $\mathcal{B}$ of 2.3 has as its total elements only the infinite sequences. Modify the construction of $\mathcal{B}$ to another neighbourhood system $\mathcal{C}$ which has *both* the finite and infinite sequences as total elements. (Hint: $\mathcal{B} \subseteq \mathcal{C}$.) Show that there is an approximable map $xy$ on elements naturally extending ordinary juxtaposition of sequences. (Hint: Write $01001$ for a *total* finite sequence and $01001\perp$ for the corresponding finite partial element. Remember to distinguish between $\Lambda$ (the total empty sequence) and $\perp$ (the undefined sequence). The definition should work out so that if $x$ is an infinite sequence (hence, total), then $xy = x$ for all $y$. What will $xy$ equal if $x$ is not total? In other words, the construction possesses a rather strong left-to-right bias.)

**EXERCISE 2.22.** (For set theorists). We have remarked in Exercise 1.18 and in Exercise 2.11 that any domain $|D|$, as a family of sets (in fact, a family of subsets of the set $D$ itself), is closed under the intersection of an arbitrary non-empty sub family and under the union of any directed sub family. For those familiar with the subject matter, the example of the (proper) ideals of a commutative ring (with unit) is also seen to be such a family. What is the abstract situation? Let $\mathbf{C}$ be *any* family of sets with these closure properties. It is to be shown that $\mathbf{C}$ is inclusion-isomorphic to a domain. (Hint: Let $\Delta$ be the set of finite sets included in sets in $\mathbf{C}$. For $F \in \Delta$, define its "closure" by the equation:

$$\overline{F} = \bigcap \{ X \in \mathbf{C} \mid F \subseteq X \}.$$

Every $\overline{F} \in \mathbf{C}$, and these will prove to be the "finite" elements of $\mathbf{C}$. The neighbourhood system $\mathcal{D}$ over $\Delta$ can be taken to be the sets of the form

$$C(F) = \{ G \in \Delta \mid F \subseteq \overline{G} \}$$

for $F \in \Delta$. Notice that for all $X \in \mathbf{C}$

$$X = \bigcup \{ \overline{F} \mid F \subseteq X \text{ and } F \in \Delta \}.$$)

Check that approximable functions on these families are just those preserving directed unions.
