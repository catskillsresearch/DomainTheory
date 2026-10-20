# Domain equations

The major reason for introducing the theory of domains is to have a notion of *computability* incorporating both finite and infinite elements. In our many examples already explored we have seen how functions (functionals, operators, combinators) can be defined on domains; owing to the property of *approximability (continuity)* of these functions, we have also seen how they can be "calculated" by finite approximation. In this lecture further examples of domains will be constructed -- especially domains having infinite elements, which can be introduced in a variety of ways giving rise to interesting structural possibilities. The next lecture then treats a precise notion of *computability* appropriate to these domains; while the last lecture opens up new methods of domain construction.

**EXAMPLE 6.1**. Let $D$ be fixed as a given domain. We are now familiar with a useful construct like $D \times D$ whose elements are ordered pairs $\langle x, y \rangle$ of elements $x, y$ of $D$. The question is: can this construct be iterated? The answer is obviously yes, since $D \times (D \times D)$ and $(D \times D) \times (D \times D)$ and so on can be formed with elements $\langle x, \langle y, z \rangle \rangle$ and $\langle \langle u, v \rangle, \langle x, y \rangle \rangle$ and the like. But the real question is: can the construct be iterated *indefinitely*? AND can the results be collected together into a *single* domain? The answer is yes, but it requires a bit of work to get it right. The method to be introduced will be open to many variations, so more than one answer is possible, giving non-isomorphic domains.

In order to collect all the iterates into one large domain we give ourselves first a very big domain inside of which the desired family of neighbourhoods will be found. There are many ways to make this choice, and we are fixing on one that will keep the notation simple. We have often used binary sequences for examples and constructions, but for this example let us use
ternary sequences. Let $\Sigma = \{0, 1, 2\}$ and let $\Sigma^*$ be all finite sequences from this three-letter alphabet. We will select subsets of $\Sigma^*$ for our neighbourhoods. As $\Sigma^*$ is countably infinite, it is without much loss of generality to assume that $\mathcal{D}$ is a neighbourhood system over $\Delta$, where we take $\Delta \subseteq \Sigma^*$. Also without loss of generality we can assume $\emptyset \notin \mathcal{D}$. (Why?)

We wish to find another set $\Gamma \subseteq \Sigma^*$ to be the set of tokens for the new domain. After we find it, we will still have to say just which $X \subseteq \Gamma$ are appropriate for the structure we want.

The totality $\{X \mid X \subseteq \Sigma^*\}$ is, as a powerset, isomorphic to the set of elements of a domain: a point we have remarked several times. So, by the Fixed-Point Theorem we know there is a set $\Gamma \subseteq \Sigma^*$ where

$$
\Gamma = 0\Delta \cup 1\Gamma \cup 2\Gamma.
$$

In fact $\Gamma = \{1, 2\}^* 0\Delta$, because we can say:

$$
\{1, 2\}^* = \{\Lambda\} \cup 1\{1, 2\}^* \cup 2\{1, 2\}^*.
$$

The domain we are looking for will be found as a domain $\mathcal{D}^{\S}$ over $\Gamma$. The reason for splitting $\Gamma$ up, as shown in the equation above, is to ensure that if $X, Y \in \mathcal{D}^{\S}$ are two neighbourhoods in the system $\mathcal{D}^{\S}$, then $1X \cup 2Y$ has a chance of being also in $\mathcal{D}^{\S}$ because

$$
1X \cup 2Y \subseteq \Gamma.
$$

This will make $\mathcal{D}^{\S} \times \mathcal{D}^{\S}$ isomorphic to a part of $\mathcal{D}^{\S}$. If we make $\mathcal{D}$ also isomorphic to a part of $\mathcal{D}^{\S}$, then all the iterated products will be contained in $\mathcal{D}^{\S}$.

What is a neighbourhood system? Just a set of sets. But $\mathcal{P}\mathcal{P}\Sigma^*$ is a domain (as a power set) and because $\Gamma \subseteq \Sigma^*$, we find

$$
\mathcal{D}^{\S} \in \mathcal{P}\mathcal{P}\Sigma^*
$$

as an element. But elements of domains can often be defined by fixed-point equations. Indeed we will introduce $\mathcal{D}^{\S}$ this way:

$$
\mathcal{D}^{\S} = \{\Gamma\} \cup \{0X \mid X \in \mathcal{D}\} \cup \{1X \cup 2Y \mid X, Y \in \mathcal{D}^{\S}\}.
$$

The reader should stop to think why $\mathcal{D}^{\S}$ can be immediately seen to exist by writing such an equation. Of course another way to describe $\mathcal{D}^{\S}$ is to say it is the least family of sets containing (i) the set $\Gamma$, (ii) the sets $0X$ for $X$ in the given system $\mathcal{D}$, and (iii) sets $1X \cup 2Y$ whenever it already contains $X$ and $Y$ (closure
under a set-forming operation). By saying "least" we mean (iv) nothing else belongs to $\mathcal{D}^{\S}$ except as allowed by (i)–(iii); this makes the truth of the equation for $\mathcal{D}^{\S}$ clear. So $\mathcal{D}^{\S}$ exists as a family of sets, but what good is it?

By our construction of $\Gamma$, all the sets we put into $\mathcal{D}^{\S}$ are subsets of $\Gamma$ (why?); so $\mathcal{D}^{\S}$ has a chance of being a system over $\Gamma$ if we can check the closure under intersection. So suppose $Z \subseteq X \cap Y$ where $Z, X, Y \in \mathcal{D}^{\S}$; we want to show $X \cap Y \in \mathcal{D}^{\S}$. We argue by induction on the number of steps required to put $X$ and $Y$ into $\mathcal{D}^{\S}$ by (i)–(iii). There are several cases.

If $X = \Gamma$ or $Y = \Gamma$, there is nothing to prove, because both sets are subsets of $\Gamma$. We note that $\emptyset \notin \mathcal{D}^{\S}$, because (i)–(iii) cannot introduce $\emptyset$ as a member of $\mathcal{D}^{\S}$. So, if $X = 0A$ for $A \in \mathcal{D}$, then $Y$ must have this form also (if it is not $\Gamma$), because

$$
0A \cap (1B \cup 2C) = \emptyset.
$$

(That is, if $Y$ had the form (iii), then $Z = \emptyset$ would be a consequence, which is impossible.) Thus, if $X = 0A$ for $A \in \mathcal{D}$, then $Y = 0B$ for some $B \in \mathcal{D}$. But by the same reasoning $Z = 0C$ for some $C \in \mathcal{D}$ also. But the relationship $0C \subseteq 0A \cap 0B$ is equivalent to $C \subseteq A \cap B$. We see, therefore, that $A \cap B \in \mathcal{D}$, and so

$$
X \cap Y = 0A \cap 0B = 0(A \cap B)
$$

must belong to $\mathcal{D}^{\S}$.

The final case has $X, Y, Z$ all of the form (iii):

$$
X = 1A_1 \cup 2A_2,
$$

$$
Y = 1B_1 \cup 2B_2, \text{ and}
$$

$$
Z = 1C_1 \cup 2C_2.
$$

We can think of the $A_i$ and $B_i$ put into $\mathcal{D}^{\S}$ earlier and the intersection result as being already established for them. But the relationship $Z \subseteq X \cap Y$ is equivalent to $C_i \subseteq A_i \cap B_i$ for $i = 1, 2$. Therefore $A_i \cap B_i \in \mathcal{D}^{\S}$, and so does

$$
X \cap Y = (1A_1 \cup 2A_2) \cap (1B_1 \cup 2B_2) = 1(A_1 \cap B_1) \cup 2(A_2 \cap B_2).
$$
We have now seen that $D^\S$ is a neighbourhood system, but why was it constructed that way? The reason is simply this isomorphism (or domain equation):

$$
D^\S \cong D + (D^\S \times D^\S),
$$

as can be seen by reference to the equation for $D^\S$ and the definitions of $+$ and $\times$. What are the elements of $D^\S$? There is always

$$
\bot = \{\Gamma\}.
$$

Next if $x \in |D|$ we define

$$
x^\S = \{\Gamma\} \cup \{0 X \mid X \in x\}.
$$

That gives an isomorphic injection

$$
\lambda x.\, x^\S : D \to D^\S.
$$

Then for $x, y \in |D^\S|$ we can define

$$
\langle x, y \rangle = \{\Gamma\} \cup \{1X \cup 2Y \mid X \in x \text{ and } Y \in y\}.
$$

We have another isomorphic injection

$$
\lambda x, y.\, \langle x, y \rangle : D^\S \times D^\S \to D^\S.
$$

Indeed by looking at the neighbourhood definition of $D^\S$ we conclude that the *finite* elements of $D^\S$ are exactly those that are either of the form (i) $\bot$, or (ii) $a^\S$, where $a$ is finite in $|D|$, or (iii) $\langle a, b \rangle$, where $a$ and $b$ are previously obtained finite elements of $|D^\S|$.

Suppose $a, \ldots, f$ are finite in $|D|$. We can picture the element

$$
u = \langle \langle a^\S, \langle \langle b^\S, c^\S \rangle, d^\S \rangle \rangle, \langle e^\S, f^\S \rangle \rangle
$$

in $|D^\S|$ as a tree:

```
              u
             /   \
            /     \
           ·       ·
          / \     / \
         a   ·   e   f
            / \
           ·   d
          / \
         b   c
Note that the tree has binary branching with the elements of $|D|$ at the ends of the branches. Any such tree could be given a notation as an element of $|D^{\S}|$. The finite elements of $|D^{\S}|$ correspond exactly to such finite trees.

What of the infinite elements of $|D^{\S}|$? Are there infinite trees? Let $a, b \in |D^{\S}|$ be any elements of $|D^{\S}|$. Since pairing is an approximable mapping, we can solve the fixed-point equation

$$
v = \langle a, \langle b, v \rangle \rangle.
$$

In pictures we can diagram $v$ roughly as:

```
        v
         \
          · — a
           \
            · — b
             \
              · — a
               \
                · — b
                 \
                  · — a
                   \
                    · — b
                     \
                      · — a
                       \
                        ··· etc.
```

The word is “roughly” here, since if $a$ or $b$ were not in the $|D|$ part of $|D^{\S}|$, then in the diagram the letters “a” and “b” should be replaced by the corresponding tree diagrams for $a$ and $b$.

Suppose that $a$ and $b$ are finite. Then we can easily see that the infinite tree $v$ is the limit of the following sequence of finite trees:

$$
v_0 = \bot,
$$

$$
v_{n+1} = \langle a, \langle b, v_n \rangle \rangle,
$$

and

$$
v = \bigcup_{n=0}^{\infty} v_n.
$$
The reader should think how to explain from tree diagrams the approximation relation $v_n \sqsubseteq v$ and more general such relationships.

We could call $D^\S$ a tree algebra over $D$. There may be others. A general one is a structure of the form

$$
\langle E, \text{in}, \text{pair} \rangle,
$$

where

$$
\text{in} : D \to E, \text{ and}
$$

$$
\text{pair} : E \times E \to E.
$$

The algebra

$$
\langle D^\S, \lambda x.\, x^\S, \lambda x, y.\, \langle x, y \rangle \rangle,
$$

however, is a very special one: it is "minimal" among all tree algebras over $D$ in a sense we shall have to make precise.

To do this think of how $E$ and $D^\S$ can differ. In view of the isomorphism that $D^\S$ satisfies, the injection of $D$ and the pairing are one-one, so no "information" is lost by these mappings. The same may not at all be true of $E$, but it is reasonable to think that at least we can define an approximable mapping $g : D^\S \to E$ where

$$
(1) \quad g(\bot) = \bot_E,
$$

$$
(2) \quad g(x^\S) = \text{in}(x), \text{ for } x \in |D|, \text{ and}
$$

$$
(3) \quad g(\langle x, y \rangle) = \text{pair}(g(x), g(y)), \text{ for } x, y \in |D^\S|.
$$

By what we said earlier, $g$ will be uniquely determined by (1)–(3), because these equations tell us exactly how to calculate $g$ on all finite elements of $|D^\S|$. An approximable mapping is always determined by its action on the finite elements. But why does $g$ exist?

It would not be too hard to give an inductive construction of $g$ as a neighbourhood relation, but a fixed-point equation is easier to write down for the same purpose. We need, though, to have the inverse ("predecessor") functions:
$$
\text{out} : D^\S \to D
$$

$$
\text{proj}_i : D^\S \to D^\S, \text{ for } i = 0, 1,
$$

where

$$
\text{out}(x^\S) = x,
$$

$$
\text{proj}_0(\langle x, y \rangle) = x, \text{ and}
$$

$$
\text{proj}_1(\langle x, y \rangle) = y.
$$

We also need

$$
\text{atom} : D^\S \to T,
$$

where

$$
\text{atom}(x^\S) = \mathrm{true}, \text{ and}
$$

$$
\text{atom}(\langle x, y \rangle) = \mathrm{false}.
$$

We can then write

$$
g(x) = \text{cond}\bigl(\text{atom}(x),\, \text{in}(\text{out}(x)),\, \text{pair}(g(\text{proj}_0(x)),\, g(\text{proj}_1(x)))\bigr).
$$

This $g$ exists by fixed-point theory, and it satisfies (1)–(3) by what we know about the structure of $|D^\S|$. As we said, $g$ is unique because the values on finite elements are fixed.

In algebraic language $g$ is a *homomorphism* of tree algebras; and $D^\S$ is called an *initial algebra*, because for any tree algebra $E$ there is a unique homomorphism $g : D^\S \to E$. We note at once that any two initial algebras are isomorphic. For if $D^*$ were another, there would exist homomorphisms in both directions between $D^\S$ and $D^*$. But the compositions of homomorphisms are again homomorphisms, and in the case of $D^\S$ if we go from $D^\S$ to $D^*$ and back to $D^\S$, the result must be the identity. The reason is that the identity can be the only homomorphism of an initial algebra into itself. We thus have a precise meaning of the minimal character of $D^\S$. But note it still took a construction to show that the domain $D^\S$ exists. $\square$
**EXAMPLE 6.2.** Our staple examples $B$ and $C$ satisfy “domain equations” in the form of isomorphisms as we have previously seen. Indeed

$$
B \cong B + B, \text{ and}
$$

$$
C \cong \{\{\Lambda\}\} + C + C,
$$

where if we liked we could construct both systems over $\{0,1\}^*$ and have:

$$
B = \{\{0,1\}^*\} \cup \{0X \mid X \in B\} \cup \{1X \mid X \in B\}, \text{ and}
$$

$$
C = \{\{0,1\}^*\} \cup \{\{\Lambda\}\} \cup \{0X \mid X \in C\} \cup \{1X \mid X \in C\}.
$$

We leave to the exercises the explanations of what kinds of algebras $B$ and $C$ are and why they are initial. Here we want to propose a simple, yet interesting generalization of $B$.

Consider this domain equation:

$$
A \cong A^n + A^n,
$$

where $A^n$ stands for the $n$-fold cartesian power of $A$. We can, with the aid of some encoding solve this equation as a neighbourhood system over $\{0,1\}^*$ as follows:

$$
A = \{\{0,1\}^*\} \cup \bigcup_{i=0,1} \left\{ i \bigcup_{j < n} 1^j 0 X_j \mid X_j \in A \text{ for all } j < n \right\}.
$$

For instance, if $n = 3$, then a typical neighbourhood in $A$ is something like

$$
00X_0 \cup 010X_1 \cup 0110X_2,
$$

where $X_0, X_1, X_2 \in A$. The first ‘0’ could also be a ‘1’ in front of each of the terms.

In words, an element of $A$ (other than $\bot$) is an $n$-tuple of elements of $A$: but there are two separate copies of these, the left one and the right one. We can write for $a \in |A|$

$$
a = \pm \langle a_0, a_1, \ldots, a_{n-1} \rangle,
$$

where $+$ is chosen if $a$ is on the right, and $-$ if on the left. As a tree diagram $a$ might look like this for $n = 3$:
```
                         a  +
                        / | \
                       + a₁− +
                      /|\ /|\ /|\
                     + − − + + a₁₂− − + −
                    etc. etc. etc.
```

That is, $a$ is an infinite ternary tree with $+$ or $-$ labels at each node. If each node (subtree) is truly infinite, the element is *total*; if $\perp$ is ever encountered, it is only *partial*; if every branch ends with $\perp$, the tree is a *finite element* of $|A|$.

What can be done with such trees? Let $\sigma \in \{0, 1, \ldots, n-1\}^*$ be a finite sequence of "digits" each less than $n$. We let $\Sigma = \{0, 1, \ldots, n-1\}$. We can define for $a \in |A|$ the operation $\sigma \mapsto a\sigma$ by recursion on $\sigma$:

$$
a \Lambda = a, \text{ and}
$$

$$
a i \sigma = (a_i) \sigma.
$$

The $a\sigma$ are just the *subtrees* of $a$ with $\sigma$ as a *selector*. We also have a map

$$
\mathrm{pos} : A \to T
$$

where

$$
\mathrm{pos}(+\langle a_0, a_1, \ldots, a_{n-1} \rangle) = \mathrm{true}, \text{ and}
$$

$$
\mathrm{pos}(-\langle a_0, a_1, \ldots, a_{n-1} \rangle) = \mathrm{false}.
$$

We say that a (total) tree $a$ is *eventually periodic* iff the set $\{a\sigma \mid \sigma \in \Sigma^*\}$ is finite. The result is that the "language"

$$
L_a = \{\sigma \in \Sigma^* \mid \mathrm{pos}(a\sigma) = \mathrm{true}\}
$$

corresponding to an eventually periodic tree is always a *regular event* of automata theory, and every such language has this form. In fact, $a$ just represents the initial state of an automaton, and $a\sigma$ represents the state after "reading" a tape $\sigma$. $\square$
In order to formulate more generally the idea of a domain equation and initial algebra, we must introduce a small amount of the terminology of category theory. To be as specific as possible, think of systems $D$ over sets $\Delta \subseteq \Sigma^*$ with $\Sigma = \{0, 1\}$, say. They form quite an interesting category with respect to the approximable maps $f : D \to D'$. Recall that to be a category of "domains" and "maps" all that is required is an associative composition $g \circ f$ of maps with identity maps $I : D \to D$ for each domain of the category. And this we certainly have for the systems indicated. And there are many other categories waiting around: for instance, restrict systems to those where $\emptyset \notin D$. This is not much of a restriction, as every system is isomorphic to one like this. Or restrict the maps to being the strict maps $f : D \to D'$ where $f(\bot_D) = \bot_{D'}$. This is an essentially different, though related category. We shall find many others.

What examples 6.1 and 6.2 suggest is the notion of a construct which makes new domains out of old. For example, with $D$ fixed, 6.1 suggests for any domain $X$ over $\Gamma \subseteq \Sigma^*$ a domain

$$
T(X) = D + (X \times X).
$$

More specifically (converting from $\Sigma = \{0, 1, 2\}$ to $\Sigma = \{0, 1\}$) we could write

$$
T(X) = \{\Gamma'\} \cup \{0X \mid X \in D\} \cup \{10X \cup 11Y \mid X, Y \in X\},
$$

where we have $\Gamma' = 0\Delta \cup 10\Gamma \cup 11\Gamma$. (By the way, here we definitely want to assume $\emptyset \notin D$ and $\emptyset \notin X$ and to get $\emptyset \notin T(X)$.) This construct is an example of a *functor*, a notion that can be defined abstractly on any category.

**DEFINITION 6.3.** A *functor* on a category (into itself) associates with every domain $X$ in the category another domain $T(X)$ and to every map

$$
f : X \to Y
$$

another map

$$
T(f) : T(X) \to T(Y)
$$
in such a way that identity maps and compositions are preserved:

$$
T(I_X) = I_{T(X)}, \text{ and}
$$

$$
T(g \circ f) = T(g) \circ T(f),
$$

whenever $f : X \to Y$ and $g : Y \to Z$. $\square$

In the example from 6.1 we have not checked how the special **T** is a functor. The hint is that whenever $f : X \to Y$, then there is a map

$$
f \times f : X \times X \to Y \times Y.
$$

But there is also a map

$$
I_D + f \times f : D + (X \times X) \to D + (Y \times Y)
$$

and this suggests the definition of $T(f)$. The details are left to the exercises. Note that the map $T(f)$ just suggested is always strict, so **T** is a functor also for the category of strict maps.

One good reason for a little of the category-theoretic language is that the next definition becomes very neat indeed.

**DEFINITION 6.4.** A ***T*-algebra** is a domain $E$ in the category together with a map

$$
k : T(E) \to E.
$$

If $m : T(F) \to F$ is another ***T*-algebra**, then a *homomorphism* is a map $h : E \to F$ in the category such that the diagram

$$
\begin{array}{ccc}
T(E) & \xrightarrow{k} & E \\
\downarrow^{T(h)} & & \downarrow^{h} \\
T(F) & \xrightarrow{m} & F
\end{array}
$$

commutes; that is, the equation

$$
h \circ k = m \circ T(h)
$$

holds. $\square$
In our example from 6.1 a $T$-algebra is a *strict* map

$$k : D + (E \times E) \to E.$$

But such strict maps are in a one-one correspondence with pairs of (not necessarily strict) maps

$$n : D \to E \quad \text{and} \quad p : E \times E \to E.$$

And the structure $\langle E, n, p \rangle$ is what we called a tree algebra. Definition 6.4 just makes this abstract. The reader should also work out the details showing that 6.4's definition of homomorphism is just what we ought to expect.

Note that the $T$-algebras and homomorphisms form a category. (Why?) The following definition is so abstract that it could be given for any category.

**DEFINITION 6.5.** A $T$-algebra is *initial* if and only if there is a unique homomorphism from it into any other $T$-algebra. $\square$

The word "other" here is not meant to imply "distinct". For an initial algebra there is one and only one homomorphism into itself: the identity map. As we already indicated in 6.1 it is a general fact that the next proposition holds.

**PROPOSITION 6.6.** Any two initial $T$-algebras are uniquely isomorphic. $\square$

Slightly more interesting is the behaviour of $T$ on initial algebras.

**PROPOSITION 6.7.** If $i : T(D) \to D$ is an initial $T$-algebra, then so is $T(i) : T^2(D) \to T(D)$ and $i$ is the isomorphism from $T(D)$ to $D$.

**Proof:** Clearly since $T$ is a functor, the map $T(i)$ has the right mapping character to make $T(D)$ a $T$-algebra. Since $D$ is initial, we have a commuting diagram:
$$
\begin{array}{ccc}
T(D) & \xrightarrow{i} & D \\
\downarrow^{T(j)} & & \downarrow^{j} \\
T^2(D) & \xrightarrow{T(i)} & T(D)
\end{array}
$$

But we also have the trivial diagram:

$$
\begin{array}{ccc}
T^2(D) & \xrightarrow{T(i)} & T(D) \\
\downarrow^{T(i)} & & \downarrow^{i} \\
T(D) & \xrightarrow{i} & D
\end{array}
$$

It follows that $i \circ j$ is a homomorphism, so

$$
i \circ j = I_D.
$$

But then because $T$ is a functor we find:

$$
T(i) \circ T(j) = I_{T(D)},
$$

and, since $j$ is a homomorphism, we have

$$
j \circ i = I_{T(D)}.
$$

This shows that $i$ is an isomorphism. $\square$

From 6.7 we see that if we are going to have initial algebras at all we have to satisfy the domain equation

$$
D \cong T(D).
$$

But generally that is not enough to assure that $D$ is initial. There is a condition that our functors satisfy, however, which guarantees the existence of homomorphisms.

**DEFINITION 6.8.** On the category of domains and strict approximable maps a functor $T$ is *continuous on maps* if for any systems $D$ and $E$ the induced mapping

$$
\lambda f.\, T(f) : (D \to_\bot E) \to (T(D) \to_\bot T(E))
$$

is approximable.
**THEOREM 6.9.** If the functor $T$ is continuous on maps and if $D \cong T(D)$, so in particular $D$ is a $T$-algebra, then for any $T$-algebra $k : T(E) \to E$ there is a homomorphism $h : D \to E$.

*Proof:* Let $i : T(D) \to D$ make $D$ a $T$-algebra, where $j : D \to T(D)$ is the inverse so that $i$ is an isomorphism of domains. Suppose that $k : T(E) \to E$ is any $T$-algebra. A homomorphism $h : D \to E$ would satisfy

$$
h \circ i = k \circ T(h).
$$

Rewrite this equation as

$$
h = k \circ T(h) \circ j.
$$

In the domain of strict maps $(D \to E)$ this is a fixed-point equation for an approximable map

$$
\lambda h.\, k \circ T(h) \circ j
$$

by our assumption on $T$. Thus, the desired homomorphism exists. $\square$

The final question we have to answer is why in our category the minimal $D$ exist. The reason is that the functors $T$ that we have in mind possess further continuity properties on domains. This is conveniently expressed in terms of a notion of "subdomain".

**DEFINITION 6.10.** For two neighbourhood systems $D$ and $E$ we write

$$
D \triangleleft E
$$

to mean that these are neighbourhood systems over the same set of tokens $\Delta$ and not only is $D \subseteq E$ but whenever $X, Y \in D$ and $X \cap Y \in E$, then $X \cap Y \in D$. $\square$

For the subdomain relation $D \triangleleft E$ to hold, $D$ has to be a smaller family of neighbourhoods, but the notion of consistency in $D$ also has to be the same as in $E$. Note that if $D_0 \triangleleft E$ and $D_1 \triangleleft E$ then
$$
D_0 \triangleleft D_1 \text{ iff } D_0 \subseteq D_1.
$$

It is also easy to prove that the union of a directed family of subdomains of $E$ is again a subdomain. As a consequence of this remark we have:

**PROPOSITION 6.11.** For a given neighbourhood system $E$, the set of subsystems

$$
\{D \mid D \triangleleft E\}
$$

forms a domain in its own right. $\square$

The subdomain relationship implies a mapping relationship between the domains.

**PROPOSITION 6.12.** If $D \triangleleft E$, then there exists a projection pair of approximable mappings:

$$
i : D \to E \quad \text{and} \quad j : E \to D
$$

where $j \circ i = I_D$ and $i \circ j \subseteq I_E$, which are determined as element-wise functions by these equations:

$$
i(x) = \{Y \in E \mid \exists X \in x.\, X \subseteq Y\},
$$

and

$$
j(y) = y \cap D,
$$

for all $x \in |D|$ and $y \in |E|$. $\square$

The proof is left for the exercises.

**DEFINITION 6.13.** A functor $T$ is *monotone on domains* iff whenever $D \triangleleft E$, then not only do we have $T(D) \triangleleft T(E)$ but the projection pair $i, j$ of 6.12 is mapped to the same kind of projection pair $T(i), T(j)$. A monotone functor is *continuous on domains* iff whenever $E$ is a domain, then the mapping

$$
\lambda D.\, T(D) : \{D \mid D \triangleleft E\} \to \{D' \mid D' \triangleleft T(E)\}
$$

is approximable. $\square$
We can now state an existence theorem that covers in fairly wide generality the examples of this lecture.

**THEOREM 6.14.** If the functor $T$ is continuous on maps and monotone and continuous on domains, and if there is a set $\Gamma$ such that

$$\{\Gamma\} \triangleleft T(\{\Gamma\}),$$

then there exists an initial $T$-algebra.

**Proof:** We proceed as in the proof of the fixed-point theorem by iterating the functor. The assumption about $\Gamma$ means that, as a neighbourhood system, $T(\{\Gamma\})$ is a system over the same set $\Gamma$. Thus, if we iterate $T$ to form $T^n(\{\Gamma\})$, all these systems are over $\Gamma$ and indeed

$$T^n(\{\Gamma\}) \triangleleft T^{n+1}(\{\Gamma\})$$

for all $n$. We can thus introduce

$$\mathcal{D} = \bigcup_{n=0}^{\infty} T^n(\{\Gamma\}),$$

and it is easy to check that $\mathcal{D}$ is a system over $\Gamma$ and

$$T^n(\{\Gamma\}) \triangleleft \mathcal{D}$$

holds for all $n$. But then we have for all $n$:

$$T^n(\{\Gamma\}) \triangleleft T^{n+1}(\{\Gamma\}) \triangleleft T(\mathcal{D}),$$

which implies $\mathcal{D} \triangleleft T(\mathcal{D})$. But $T$ is continuous on domains, so

$$
\begin{aligned}
T(\mathcal{D}) &= T\!\left(\bigcup_{n=0}^{\infty} T^n(\{\Gamma\})\right) \\
&= \bigcup_{n=0}^{\infty} T^{n+1}(\{\Gamma\}) \\
&= \mathcal{D}.
\end{aligned}
$$
Thus, not only is $\mathcal{D}$ a $T$-algebra, but the isomorphism we get for $\mathcal{D}$ and $T(\mathcal{D})$ is just the identity mapping. We know by 6.9 that homomorphisms exist; what remains to show is that homomorphism from $\mathcal{D}$ are unique. As in the examples, we will show in effect they are determined uniquely on the finite elements of $\mathcal{D}$.

Since each $T^n(\{\Gamma\}) \triangleleft \mathcal{D}$, there are projection mappings $i_n : T^n(\{\Gamma\}) \to \mathcal{D}$ and $j_n : \mathcal{D} \to T^n(\{\Gamma\})$.

Define $\rho_n : \mathcal{D} \to \mathcal{D}$ by $\rho_n = i_n \circ j_n$. Projection pairs are always pairs of strict mappings (Why?), and so are in the category. By assumption and 6.13, the functor $T$ preserves these maps, so we have

$$
T(\rho_n) = T(i_n) \circ T(j_n) = i_{n+1} \circ j_{n+1} = \rho_{n+1}.
$$

As a neighbourhood relation $\rho_n$ can be characterized by :

$$
X \rho_n Y \quad \text{iff} \quad \exists z \in T^n(\{\Gamma\}).\; X \subseteq z \subseteq Y.
$$

We thus see that $\rho_n \subseteq \rho_{n+1}$ and

$$
\bigcup_{n=0}^{\infty} \rho_n = I_{\mathcal{D}}.
$$

Now suppose $k : T(E) \to E$ is any $T$-algebra and $h : \mathcal{D} \to E$ is a homomorphism. The mapping will satisfy the fixed-point equation

$$
h = k \circ T(h),
$$

where no other mappings need be written in because $\mathcal{D} = T(\mathcal{D})$ and so

$$
T(h) : \mathcal{D} \to T(E).
$$

We wish to show that $h$ really is the least fixed point of this equation.

Define $h_n = h \circ \rho_n : \mathcal{D} \to E$. For $n = 0$, the map $\rho_0$ is the trivial map where $\rho_0(x) = \bot_{\mathcal{D}}$ for all $x \in |\mathcal{D}|$. But $h$ must be strict, so $h_0(x) = \bot_E$ for all $x \in |\mathcal{D}|$; that is, $h_0$ is the least element of $|\mathcal{D} \to_\bot E|$. Now calculate :
$$
\begin{aligned}
k \circ T(h_n) &= k \circ T(h) \circ T(\rho_n) \\
&= h \circ \rho_{n+1} \\
&= h_{n+1} \ .
\end{aligned}
$$

This shows that the union of the $h_n$ is the least fixed point of $\lambda h.\, k \circ T(h)$. But

$$
\begin{aligned}
\bigcup_{n=0}^{\infty} h_n &= \bigcup_{n=0}^{\infty} h \circ \rho_n \\
&= h \circ \bigcup_{n=0}^{\infty} \rho_n \\
&= h \circ I_D = h,
\end{aligned}
$$

so the given $h$ is in fact the least fixed point. The homomorphism is uniquely determined, and $D$ is the initial $T$-algebra. $\square$

Having the existence of initial $T$-algebras, we can prove one more result that shows just how minimal they are. We need a lemma about projection pairs, first, that shows where sub-domains fit in. We write $D \trianglelefteq E$ as short for $D \cong D'$ for some $D' \triangleleft E$ in the following. The lemma gives a converse to 6.12.

**LEMMA 6.15.** For two neighbourhood systems $D$ and $E$, if there exist a projection pair

$$
i : D \to E \quad \text{and} \quad j : E \to D
$$

with $j \circ i = I_D$ and $i \circ j \subseteq I_E$, then $D \trianglelefteq E$ .

*Proof.* What we want to show is that $i$ maps finite elements to finite elements, and that the desired $D'$ is the image of $D$ in $E$.

Suppose $X \in D$. We can write:

$$
i(\uparrow X) = \bigcup \{ \uparrow Y \mid Y \in i(\uparrow X) \} \ .
$$

Applying $j$ to both sides we have:
$$
\uparrow X = j \circ i(\uparrow X) = \bigcup \{ j(\uparrow Y) \mid Y \in i(\uparrow X) \}.
$$

But then, since $X \in \uparrow X$, we find $X \in j(\uparrow Y)$ for some $Y \in i(\uparrow X)$. This implies

$$
\uparrow X \subseteq j(\uparrow Y); \text{ and so } i(\uparrow X) \subseteq i \circ j(\uparrow Y) \subseteq \uparrow Y.
$$

Since $\uparrow Y \subseteq i(\uparrow X)$ in any case, we conclude $i(\uparrow X) = \uparrow Y$. This proves finite elements are mapped to finite elements.

What of $\Delta$; that is, what is $i(\uparrow \Delta)$? We find, supposing $E$ to be a neighbourhood system over a set $\Delta'$, that since $\uparrow \Delta \subseteq j(\uparrow \Delta')$, then $i(\uparrow \Delta) \subseteq \uparrow \Delta'$ and so $i(\uparrow \Delta) = \uparrow \Delta'$. This means that $\Delta$ corresponds to $\Delta'$. So we have established that $\mathcal{D}$ is in an inclusion preserving one-one correspondence with a subset $\mathcal{D}'$ of $E$ where $\Delta' \in \mathcal{D}'$. But it remains to show that $\mathcal{D}'$ is a neighbourhood system and that $\mathcal{D}' \triangleleft E$ holds. All we really have to show is that $\mathcal{D}'$ is closed under intersection whenever the intersection belongs to $E$.

Suppose $Y', Z' \in \mathcal{D}'$ and $Y' \cap Z' \in E$. Let $X' = Y' \cap Z'$. We have, for suitable $Y, Z \in \mathcal{D}$,

$$
i(\uparrow Y) = \uparrow Y', \text{ and so } \uparrow Y = j(\uparrow Y'); \text{ and}
$$

$$
i(\uparrow Z) = \uparrow Z', \text{ and so } \uparrow Z = j(\uparrow Z').
$$

But $\uparrow Y' \subseteq \uparrow X'$ and $j(\uparrow Y') \subseteq j(\uparrow X')$; thus $Y \in j(\uparrow X')$. For similar reasons $Z \in j(\uparrow X')$. But then $X = Y \cap Z \in j(\uparrow X')$, and therefore $Y \cap Z \in \mathcal{D}$. (The element $j(\uparrow X')$ must be a filter.) Notice, however, that

$$
\uparrow Y \subseteq \uparrow X, \text{ and so } \uparrow Y' \subseteq i(\uparrow X); \text{ and}
$$

$$
\uparrow Z \subseteq \uparrow X, \text{ and so } \uparrow Z' \subseteq i(\uparrow X).
$$

It follows that $Y' \cap Z' = X' \in i(\uparrow X)$. On the other hand we already knew $X \in j(\uparrow X')$, which implies $i(\uparrow X) \subseteq \uparrow X'$. We may thus conclude that $i(\uparrow X) = \uparrow X'$. In other words $X' \in \mathcal{D}'$. $\square$
**THEOREM 6.16.** If on the category of domains and strict approximable maps the functor $T$ is continuous on maps, and if $D$ is an initial $T$-algebra, then for any system $E \cong T(E)$ we have $D \trianglelefteq E$.

**Proof:** There is a homomorphism $h : D \to E$. By 6.9 there is a homomorphism $g : E \to D$. Now $g \circ h : D \to D$ is also a homomorphism, so $g \circ h = I_D$ because $D$ is initial. In view of 6.15, all we have to prove now is that $h \circ g \sqsubseteq I_E$.

Let the maps $i : T(D) \to D$ and $j : D \to T(D)$ give the isomorphism for $D$, and let $u : T(E) \to E$ and $v : E \to T(E)$ do the same for $E$. By the proof of 6.9 we know

$$
g = i \circ T(g) \circ v \quad \text{and} \quad h = u \circ T(h) \circ j
$$

and each of these maps is the least fixed point of its respective equation. Let

$$
g_0 = \bot_{E \to D} \quad \text{and} \quad h_0 = \bot_{D \to E}
$$

and define by recursion

$$
g_{n+1} = i \circ T(g_n) \circ v \quad \text{and} \quad h_{n+1} = u \circ T(h_n) \circ j.
$$

By the fixed-point calculation

$$
g = \bigsqcup_{n=0}^{\infty} g_n \quad \text{and} \quad h = \bigsqcup_{n=0}^{\infty} h_n.
$$

Now we see that

$$
h_0 \circ g_0 = \bot_{E \to E},
$$

and for each $n$ that

$$
\begin{aligned}
h_{n+1} \circ g_{n+1} &= u \circ T(h_n) \circ j \circ i \circ T(g_n) \circ v \\
&= u \circ T(h_n) \circ T(g_n) \circ v \\
&= u \circ T(h_n \circ g_n) \circ v.
\end{aligned}
$$

But this means that

$$
h \circ g = \bigsqcup_{n=0}^{\infty} (h_n \circ g_n)
$$

is the least fixed point for the equation

$$
k = u \circ T(k) \circ v.
$$

But $I_E$ is one of the fixed points; whence $h \circ g \sqsubseteq I_E$ must follow. $\square$
# EXERCISES

**EXERCISE 6.17.** What are the algebras for which $C$ is initial? If $A$ of 6.2 is a generalization of $B$, what is the corresponding generalization of $C$? Prove that it exists and explain what are the algebras involved.

**EXERCISE 6.18.** With reference back to Exercise 3.16 discuss the construction of $\mathcal{D}^\infty$ as an initial algebra and as a solution to the domain equation

$$
\mathcal{D}^\infty \cong \mathcal{D} \times \mathcal{D}^\infty .
$$

(I do not know whether all solutions must be of the form $\mathcal{D}^\infty \times E$.)

**EXERCISE 6.19.** For the sake of uniformity restrict attention to systems $\mathcal{D}$ on sets $\Delta \subseteq \{0,1\}^*$, where $\Lambda \in \Delta$ and $\emptyset \notin \mathcal{D}$, and to the category of strict maps. Define sum and product by:

$$
\mathcal{D}_0 + \mathcal{D}_1 = \{\{\Lambda\} \cup 0\Delta_0 \cup 1\Delta_1\} \cup \{0X \mid X \in \mathcal{D}_0\} \cup \{1Y \mid Y \in \mathcal{D}_1\},
$$

$$
\mathcal{D}_0 \times \mathcal{D}_1 = \{\{\Lambda\} \cup 0X \cup 1Y \mid X \in \mathcal{D}_0 \text{ and } Y \in \mathcal{D}_1\}.
$$

Are these correct up to isomorphism? Now generate all constructs $T(X)$ formed by the constants (that is, $T(X) = \mathcal{D}$ for a fixed $\mathcal{D}$), by the identity ($T(X) = X$), and by sums and products ($T_0(X) + T_1(X)$, etc.). Show that these are all functors, continuous on maps, and monotone and continuous on domains.

**EXERCISE 6.20.** For any system $\mathcal{D}$ let $\mathrm{tok}(\mathcal{D})$ be the underlying set of tokens, so that $\mathcal{D}$ is a system over $\mathrm{tok}(\mathcal{D})$. For the category of Exercise 6.19 show that the function

$$
\lambda \Gamma.\, \mathrm{tok}(T(\{\Gamma\}))
$$

is continuous on the domain $\{\Gamma \subseteq \{0,1\}^* \mid \Lambda \in \Gamma\}$, where $T$ is any of the functors generated in 6.19. Conclude that there must exist a set

$$
\Gamma = \mathrm{tok}(T(\{\Gamma\})),
$$

so that $\{\Gamma\} \triangleleft T(\{\Gamma\})$, and so 6.14 applies.
**EXERCISE 6.21.** Do the same as 6.19 and 6.20 when the functors are also allowed to be generated by the operations:

$$
D_0 \oplus D_1 = \{\{\Lambda\} \cup 0\Delta_0 \cup 1\Delta_1\} \cup \{0X \mid X \in D_0 \setminus \{\Delta_0\}\} \cup \{1Y \mid Y \in D_1 \setminus \{\Delta_1\}\},
$$

$$
D_0 \otimes D_1 = \{\{\Lambda\} \cup 0\Delta_0 \cup 1\Delta_1\} \cup \{\{\Lambda\} \cup 0X \cup 1Y \mid X \in D_0 \setminus \{\Delta_0\} \text{ and } Y \in D_1 \setminus \{\Delta_1\}\}.
$$

Generalize all of $+$, $\times$, $\oplus$, $\otimes$ to combinations of several terms, not just the binary sums and products.

**EXERCISE 6.22.** Comment on these domain equations:

$$
N \cong \{\{0\}, \{0, \Lambda\}\} \oplus N,
$$

$$
M \cong \{\{\Lambda\}\} + M,
$$

$$
N^* \cong N \oplus (N \otimes N^*).
$$

**EXERCISE 6.23.** Construe the initial solution to

$$
\mathit{Exp} \cong N \oplus ((\mathit{Exp} \times \mathit{Exp}) + (\mathit{Exp} \times \mathit{Exp}))
$$

as a “syntactical domain” of expressions generated from infinitely many “variables” by means of two binary “operation symbols”. Given an algebra $D$ with two operations

$$
u : D \times D \to D \quad \text{and} \quad v : D \times D \to D,
$$

show how any strict map $s : N \to D$ determines a unique map

$$
\mathit{val}(s) : \mathit{Exp} \to D
$$

that can be regarded as the “evaluation of an expression”.

**EXERCISE 6.24.** Show that there must exist domains satisfying:

$$
D \cong D + (D \times E), \quad \text{and}
$$

$$
E \cong D + E,
$$

by using a double fixed-point method. First decide what the underlying set of tokens should be, and then define $D$ and $E$ by simultaneous fixed points. (Syntactical domains as in 6.23 may very well require several simultaneous equations.)
**EXERCISE 6.25.** For a projection pair $g : \mathcal{D} \to \mathcal{E}$ and $h : \mathcal{E} \to \mathcal{D}$ show that for $x \in |\mathcal{D}|$ and $y \in |\mathcal{E}|$ we have:

$$g(x) \sqsubseteq y \text{ iff } x \sqsubseteq h(y).$$

Thus, conclude that:

$$h(y) = \bigsqcup \{x \in |\mathcal{D}| \mid g(x) \sqsubseteq y\}, \quad \text{and}$$

$$g(x) = \bigsqcap \{y \in |\mathcal{E}| \mid x \sqsubseteq h(y)\},$$

for all $x \in |\mathcal{D}|$ and $y \in |\mathcal{E}|$. So each of the functions determines the other. In the first equation check that the set on the right is directed, and in the second equation that the set on the right is non empty. Prove also that $g$ maps consistent sets to consistent sets and preserves $\bigsqcup$ (not just directed unions).

**EXERCISE 6.26.** For systems $\mathcal{D}$ as in 6.19 define

$$\mathcal{D}_\perp = \{ \{\Lambda\} \cup 0\Delta \} \cup \{ 0X \mid X \in \mathcal{D} \}.$$

Describe the construct in terms of elements. Is this a suitable functor? Prove that

$$\mathcal{D}_\perp \oplus \mathcal{E}_\perp \cong \mathcal{D} + \mathcal{E}.$$

What is

$$\mathcal{D}_\perp \otimes \mathcal{E}_\perp \cong \ ??$$

**EXERCISE 6.27.** Which of the following relationships are true:

$$(\mathcal{D} \otimes \mathcal{E}) \trianglelefteq (\mathcal{D} \times \mathcal{E}) \ ; \quad \mathcal{D} \trianglelefteq \mathcal{D} \times \mathcal{E} \ ;$$

$$(\mathcal{D} \oplus \mathcal{E}) \trianglelefteq (\mathcal{D} + \mathcal{E}) \ ; \quad \mathcal{D} \trianglelefteq \mathcal{D} \oplus \mathcal{E} \ ;$$

$$(\mathcal{D} \to_\perp \mathcal{E}) \trianglelefteq (\mathcal{D} \to \mathcal{E}) \ ; \quad \mathcal{D} \trianglelefteq \mathcal{D} \otimes \mathcal{E} \ ?$$

**EXERCISE 6.28.** (Suggested by G. Plotkin). Show that if $\mathcal{D}$ and $\mathcal{E}$ are *finite* systems and

$$\mathcal{D} \trianglelefteq \mathcal{E} \trianglelefteq \mathcal{D} \ ,$$

then $\mathcal{D} \cong \mathcal{E}$. Need the same be true of infinite systems?
**EXERCISE 6.29.** Generalize $+$ and $\times$ to infinitary operations on domains:

$$\sum_{n=0}^{\infty} D_n \quad \text{and} \quad \prod_{n=0}^{\infty} D_n.$$

Would a similar generalization be possible for $\oplus$ and $\otimes$?

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/AlgHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/AlgHom.lean)
- [NeighbourhoodSystems/DomainEquations/C_bot_eq_strBot_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/C_bot_eq_strBot_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Calg.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Calg.lean)
- [NeighbourhoodSystems/DomainEquations/Category.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Category.lean)
- [NeighbourhoodSystems/DomainEquations/Category/notation4.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Category/notation4.lean)
- [NeighbourhoodSystems/DomainEquations/Category/notation6.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Category/notation6.lean)
- [NeighbourhoodSystems/DomainEquations/CisInitial.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/CisInitial.lean)
- [NeighbourhoodSystems/DomainEquations/Cobj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Cobj.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/Basic/notation2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/Basic/notation2.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/Subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/Subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/_root_u2eDomainTheoryu2eNeighborhoodu2eNeighborhoodSystemu2eext.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/_root_u2eDomainTheoryu2eNeighborhoodu2eNeighborhoodSystemu2eext.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/antisymm.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/antisymm.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/refl.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/refl.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/subsystem_iff_subset_of_common.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/subsystem_iff_subset_of_common.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/trans.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/trans.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition613.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition613/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/ContinuousOnDomains.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition613/ContinuousOnDomains.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/MonotoneAt.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition613/MonotoneAt.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/MonotoneOnDomains.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition613/MonotoneOnDomains.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/continuousOnDomains_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition613/continuousOnDomains_id.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/monotoneOnDomains_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition613/monotoneOnDomains_id.lean)
- [NeighbourhoodSystems/DomainEquations/Definition613/targetFam.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition613/targetFam.lean)
- [NeighbourhoodSystems/DomainEquations/Definition63.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition63.lean)
- [NeighbourhoodSystems/DomainEquations/Definition63Inst2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition63Inst2.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition68.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition68/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/ContinuousOnMaps.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition68/ContinuousOnMaps.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/ContinuousOnMapsu2eisStrict_map.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition68/ContinuousOnMapsu2eisStrict_map.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/continuousOnMaps_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition68/continuousOnMaps_id.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/idEndofunctor.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition68/idEndofunctor.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/idEndofunctor_map.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition68/idEndofunctor_map.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/idEndofunctor_obj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition68/idEndofunctor_obj.lean)
- [NeighbourhoodSystems/DomainEquations/Definition68/toStrictMap_toStrictFilter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition68/toStrictMap_toStrictFilter.lean)
- [NeighbourhoodSystems/DomainEquations/DomainObj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/DomainObj.lean)
- [NeighbourhoodSystems/DomainEquations/Dsharp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Dsharp.lean)
- [NeighbourhoodSystems/DomainEquations/Dsharp_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Dsharp_master.lean)
- [NeighbourhoodSystems/DomainEquations/Dsharp_mem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Dsharp_mem.lean)
- [NeighbourhoodSystems/DomainEquations/Endofunctor.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Endofunctor.lean)
- [NeighbourhoodSystems/DomainEquations/Example61.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/Gamma.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/Gamma.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/MemS.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/MemS.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/embL.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/embL.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/embPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/embPair.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/embR.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/embR.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/embZero.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/embZero.lean)
- [NeighbourhoodSystems/DomainEquations/Example62.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/BB.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/BB.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/B_domain_equation.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/B_domain_equation.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/B_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/B_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/bbEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/bbEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_cone.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/embBit_cone.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_eq_prepend.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/embBit_eq_prepend.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/embBit_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/embBit_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_inter_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/embBit_inter_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/embBit_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_ne_univ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/embBit_ne_univ.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/embBit_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/embBit_subset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/embBit_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/fromBB.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/fromBB.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/fromBB_mem_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/fromBB_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/fromBB_mem_embT.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/fromBB_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/fromBB_toBB.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/fromBB_toBB.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/memB_cases.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/memB_cases.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/memB_embBit.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/memB_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/memB_embBit_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/memB_embBit_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/mem_embBit.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/mem_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/nil_not_mem_embBit.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/nil_not_mem_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/sum_mem_inj₀_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/sum_mem_inj₀_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/sum_mem_inj₁_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/sum_mem_inj₁_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/sum_mem_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/sum_mem_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/toBB.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/toBB.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/toBB_fromBB.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/toBB_fromBB.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/toBB_mem_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/toBB_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainEquations/Example62/toBB_mem_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62/toBB_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/AAsys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/AAsys.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/A_domain_equation.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/A_domain_equation.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/Apow.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/Apow.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/Asys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/Asys.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/Asys_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/Asys_master.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/Asys_mem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/Asys_mem.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/MemA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/MemA.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aaEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/aaEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₀_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₀_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₁_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_inj₁_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/aa_mem_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/apowNe.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/apowNe.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/apow_mem_prodN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/apow_mem_prodN.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/apow_mem_prodN_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/apow_mem_prodN_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/embTuple.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/embTuple_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/embTuple_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_inter_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/embTuple_inter_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/embTuple_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_ne_univ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/embTuple_ne_univ.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/embTuple_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/embTuple_subset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/embTuple_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/fromAA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/fromAA.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/fromAA_mem_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/fromAA_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/fromAA_mem_embT.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/fromAA_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/fromAA_toAA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/fromAA_toAA.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/memA_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/memA_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/memA_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/memA_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/memA_tuple_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/memA_tuple_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/mem_embTuple.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/mem_embTuple.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/mem_prodN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/mem_prodN.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/nil_not_mem_embTuple.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/nil_not_mem_embTuple.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/npow.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/npow.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/npow_mem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/npow_mem.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/npow_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/npow_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/prodN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/prodN.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/prodN_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/prodN_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/prodN_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/prodN_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/prodN_subset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/prodN_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/slotPre.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/slotPre.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/slotPre_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/slotPre_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/slot_list_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/slot_list_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/tag_eq_of_subset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/tag_eq_of_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/toAA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/toAA.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/toAA_fromAA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/toAA_fromAA.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/toAA_mem_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/toAA_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainEquations/Example62A/toAA_mem_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62A/toAA_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/CC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/CC.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/C_domain_equation.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/C_domain_equation.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/C_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/C_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/ccEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/ccEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/embBit_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/embBit_singleton.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/eq_master3_of_subset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/eq_master3_of_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/fromCC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/fromCC.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/fromCC_mem_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/fromCC_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/fromCC_mem_embT.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/fromCC_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/fromCC_mem_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/fromCC_mem_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/fromCC_toCC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/fromCC_toCC.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j0_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_inter_j0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j0_inter_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_inter_j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j0_inter_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_inter_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j0_inter_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j0_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_subset_j0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j0_subset_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j0_subset_master3.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j0_subset_master3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j1_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_inter_j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j1_inter_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_inter_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j1_inter_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j1_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_subset_j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j1_subset_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j1_subset_master3.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j1_subset_master3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j2_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2_inter_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j2_inter_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j2_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2_subset_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j2_subset_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/j2_subset_master3.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/j2_subset_master3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/master3.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/master3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/master3_inter_j0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/master3_inter_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/master3_inter_j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/master3_inter_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/master3_inter_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/master3_inter_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/memC_cases.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/memC_cases.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/memC_embBit.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/memC_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/memC_embBit_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/memC_embBit_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/none_mem_master3.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/none_mem_master3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/none_not_mem_j0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/none_not_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/none_not_mem_j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/none_not_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/none_not_mem_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/none_not_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/singleton_nil_inter_embBit.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/singleton_nil_inter_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/singleton_nil_ne_embBit.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/singleton_nil_ne_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/singleton_nil_ne_univ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/singleton_nil_ne_univ.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/sum3.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/sum3.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/sum3_mem_j1_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/sum3_mem_j1_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/sum3_mem_j2_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/sum3_mem_j2_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/sum3_mem_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/sum3_mem_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t0_mem_j0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t0_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t0_not_mem_j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t0_not_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t0_not_mem_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t0_not_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t1_mem_j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t1_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t1_not_mem_j0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t1_not_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t1_not_mem_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t1_not_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t2_mem_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t2_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t2_not_mem_j0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t2_not_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/t2_not_mem_j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/t2_not_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/toCC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/toCC.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/toCC_fromCC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/toCC_fromCC.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/toCC_mem_j0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/toCC_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/toCC_mem_j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/toCC_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/toCC_mem_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/toCC_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/Example62C/unitSys_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62C/unitSys_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/EventuallyPeriodic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/EventuallyPeriodic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/Tree.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/Tree.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/child.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/child.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/eventuallyPeriodic_iff_isRegular.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/eventuallyPeriodic_iff_isRegular.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/isRegular_iff_exists_eventuallyPeriodic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/isRegular_iff_exists_eventuallyPeriodic.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/mem_treeLang.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/mem_treeLang.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/pos.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/pos.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/pos_select.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/pos_select.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/select.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/select.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/select_append.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/select_append.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/select_apply.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/select_apply.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/select_cons.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/select_cons.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/select_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/select_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang_eq_pos.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang_eq_pos.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang_select.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example62Regular/treeLang_select.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617/descAlgHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617/descAlgHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617/descMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617/descMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/CCn.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/CCn.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/CfinIsInitial.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/CfinIsInitial.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cfin_domain_equation.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cfin_domain_equation.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn_bot_eq_strBotN_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn_bot_eq_strBotN_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn_domain_equation.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn_domain_equation.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn_mem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn_mem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cn_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cnalg.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cnalg.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/CnisInitial.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/CnisInitial.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cnobj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cnobj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cnobj_sys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Cnobj_sys.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/SigTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/SigTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Strn.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Strn.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Tsig.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Tsig.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Tsig_map_val.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Tsig_map_val.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/Tsig_obj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/Tsig_obj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/ccEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/ccEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/ccEquiv_apply.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/ccEquiv_apply.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/ccEquiv_comp_symm.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/ccEquiv_comp_symm.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/ccEquiv_symm_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/ccEquiv_symm_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/cnStr.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/cnStr.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN_ne_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN_ne_singleton.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN_subset_coneN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN_subset_coneN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN_trichotomy.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/coneN_trichotomy.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_mem_embA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_mem_embA.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_not_mem_embA_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_not_mem_embA_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_not_mem_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_not_mem_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_strBot.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_strBot.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_strElem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/consMapN_strElem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descAlgHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descAlgHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descAlgHom_uniq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descAlgHom_uniq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descComm.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descComm.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descE.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descF_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descF_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_hcone.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_hcone.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_hsing.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_hsing.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_satisfiesRec.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_satisfiesRec.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_strBot.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_strBot.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_strElem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_strElem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_strict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descMap_strict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descVal.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descVal.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descVal_append.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descVal_append.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/descVal_mono_z.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/descVal_mono_z.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_coneN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_coneN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_eq_embA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_eq_embA.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_eq_prependN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_eq_prependN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_inter_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_inter_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_ne_univ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_ne_univ.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_singleton.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_subset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/embA_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/eq_masterSig_of_subset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/eq_masterSig_of_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/fromCC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/fromCC.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/fromCC_mem_embA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/fromCC_mem_embA.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/fromCC_mem_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/fromCC_mem_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/fromCC_toCC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/fromCC_toCC.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/genKey.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/genKey.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/genKey0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/genKey0.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/genKeyBot.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/genKeyBot.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/isStrict_sumMapSig.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/isStrict_sumMapSig.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jU.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jU.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jU_inter_jc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jU_inter_jc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jU_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jU_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jU_subset_masterSig.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jU_subset_masterSig.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_eq_jc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_eq_jc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_inter_jc_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_inter_jc_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_inter_jc_same.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_inter_jc_same.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_subset_jc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_subset_jc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_subset_masterSig.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/jc_subset_masterSig.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/liftCn.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/liftCn.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/liftCn_strBot.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/liftCn_strBot.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/liftCn_strElem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/liftCn_strElem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/map_ext_Cn.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/map_ext_Cn.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/masterSig.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/masterSig.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/masterSig_inter_jU.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/masterSig_inter_jU.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/masterSig_inter_jc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/masterSig_inter_jc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_cases.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_cases.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_coneN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_coneN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_embA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_embA.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_embA_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_embA_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_prependN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_prependN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/memCn_singleton.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_coneN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_coneN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_embA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_embA.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_jU.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_jU.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_prependN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_prependN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_subset_jU_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_subset_jU_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_subset_jc_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/mem_subset_jc_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/nestedOrDisjointN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/nestedOrDisjointN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/nil_not_mem_embA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/nil_not_mem_embA.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/none_mem_masterSig.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/none_mem_masterSig.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/none_not_mem_jU.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/none_not_mem_jU.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/none_not_mem_jc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/none_not_mem_jc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/not_coneN_subset_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/not_coneN_subset_singleton.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/prependN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/prependN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/prependN_coneN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/prependN_coneN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/prependN_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/prependN_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/prependN_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/prependN_singleton.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/rec_determines.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/rec_determines.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/singleton_coneN_nd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/singleton_coneN_nd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/singleton_nil_inter_embA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/singleton_nil_inter_embA.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/singleton_nil_ne_embA.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/singleton_nil_ne_embA.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/singleton_nil_ne_univ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/singleton_nil_ne_univ.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/singleton_subset_coneN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/singleton_subset_coneN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sinjC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sinjC.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sinjC_mem_jc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sinjC_mem_jc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sinjC_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sinjC_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sinjU.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sinjU.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sinjU_mem_jU.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sinjU_mem_jU.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/strBotN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/strBotN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/strElemN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/strElemN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig_sinjC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig_sinjC.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig_sinjU.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumMapSig_sinjU.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumSig.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumSig.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumSig_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumSig_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumSig_mem_jc_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumSig_mem_jc_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumSig_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/sumSig_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tc_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tc_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tc_mem_jc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tc_mem_jc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tc_mem_jc_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tc_mem_jc_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tc_not_mem_jU.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tc_not_mem_jU.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC_consMapN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC_consMapN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC_fromCC.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC_fromCC.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC_mem_jU.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC_mem_jU.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC_mem_jc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC_mem_jc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC_strElemN_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/toCC_strElemN_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tsigMapHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tsigMapHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tsigMapHom_val.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tsigMapHom_val.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tsigObj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tsigObj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tsigObj_sys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tsigObj_sys.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tu.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tu.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tu_mem_masterSig.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tu_mem_masterSig.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Gen/tu_not_mem_jc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Gen/tu_not_mem_jc.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise617Inst3.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise617Inst3.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise618.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise618.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise618/descAlgHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise618/descAlgHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise618/descMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise618/descMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise618/descMap_strict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise618/descMap_strict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/embF_ne_sumTokMaster.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/embF_ne_sumTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/embF_subset_sumTokMaster.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/embF_subset_sumTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/embT_ne_sumTokMaster.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/embT_ne_sumTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/embT_subset_sumTokMaster.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/embT_subset_sumTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/fromSum.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/fromSum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/fromSum_mem_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/fromSum_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/fromSum_mem_embT.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/fromSum_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/fromSum_toSum.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/fromSum_toSum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/fstTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/fstTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/fstTok_pairTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/fstTok_pairTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/mem_fstTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/mem_fstTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/mem_pairTok_prodTokNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/mem_pairTok_prodTokNbhd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/mem_prodTokNbhd_false.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/mem_prodTokNbhd_false.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/mem_prodTokNbhd_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/mem_prodTokNbhd_nil.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/mem_prodTokNbhd_true.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/mem_prodTokNbhd_true.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/mem_sndTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/mem_sndTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/nil_mem_sumTokMaster.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/nil_mem_sumTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/pairTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/pairTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/pairTok_fstTok_sndTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/pairTok_fstTok_sndTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTokEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTokEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTokNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTokNbhd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTokNbhd_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTokNbhd_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTokNbhd_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTokNbhd_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTokNbhd_master_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTokNbhd_master_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTokNbhd_subset_iff.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTokNbhd_subset_iff.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_iso_prod.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_iso_prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_mem_iff.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_mem_prodTokNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_mem_prodTokNbhd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_mem_split.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_mem_split.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/prodTok_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sndTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sndTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sndTok_pairTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sndTok_pairTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTokEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTokEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTokMaster.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTokMaster_inter_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTokMaster_inter_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTokMaster_inter_embT.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTokMaster_inter_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_iso_sum.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_iso_sum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_embF_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_embF_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_embT.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_embT_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_embT_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_mem_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sumTok_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sum_mem_inj₀_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sum_mem_inj₀_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sum_mem_inj₁_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sum_mem_inj₁_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/sum_mem_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/sum_mem_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/toSum.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/toSum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/toSum_fromSum.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/toSum_fromSum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/toSum_mem_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/toSum_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619/toSum_mem_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619/toSum_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpr.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpr.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_continuous.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_continuous.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_continuous_mp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_continuous_mp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2emap_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2eobj_continuous.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2eobj_continuous.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2eobj_continuous_mp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2eobj_continuous_mp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2eobj_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/FExpru2eobj_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/RootedConst.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/RootedConst.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/ScottSys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/ScottSys.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/embBit_not_subset_cross.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/embBit_not_subset_cross.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/mFun.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/mFun.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/mIter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/mIter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/map.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/map.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/obj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/obj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/prod.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodMapTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodMapTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodMapTok_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodMapTok_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodMapTok_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodMapTok_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodMapTok_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodMapTok_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodMapTok_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodMapTok_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodTok_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/prodTok_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/singletonSys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/singletonSys.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/sum.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/sum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumMapTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumMapTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumMapTok_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumMapTok_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumMapTok_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumMapTok_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumMapTok_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumMapTok_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumMapTok_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumMapTok_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumTok_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/sumTok_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise619PartB/tok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise619PartB/tok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpr.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpr.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_continuous.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_continuous.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_continuous_mp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_continuous_mp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2emap_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2enaryOp_rootedConst.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2enaryOp_rootedConst.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2eobj_continuous.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2eobj_continuous.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2eobj_continuous_mp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2eobj_continuous_mp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2eobj_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/GExpru2eobj_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/RootedConst.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/RootedConst.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/gFun.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/gFun.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/gIter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/gIter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/inter_ne_of_ne_left.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/inter_ne_of_ne_left.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/inter_ne_of_ne_right.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/inter_ne_of_ne_right.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/map.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/map.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/naryOp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/naryOp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/naryOplus.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/naryOplus.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/naryOplus_singleton_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/naryOplus_singleton_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/naryOtimes.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/naryOtimes.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/naryOtimes_singleton_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/naryOtimes_singleton_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/naryProd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/naryProd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/naryProd_singleton_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/naryProd_singleton_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/narySum.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/narySum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/narySum_singleton_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/narySum_singleton_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/obj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/obj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplus.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplus.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusMapTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusMapTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusMapTok_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusMapTok_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusMapTok_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusMapTok_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusMapTok_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusMapTok_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusMapTok_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusMapTok_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_mem_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_mem_embF_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_mem_embF_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_mem_embT.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_mem_embT_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_mem_embT_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_mem_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/oplusTok_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimes.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimes.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesMapTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesMapTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesMapTok_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesMapTok_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesMapTok_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesMapTok_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesMapTok_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesMapTok_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesMapTok_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesMapTok_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok_mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok_mem_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok_mem_prod.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok_mem_prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok_mem_prod_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok_mem_prod_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise621/otimesTok_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/Cnat.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/Cnat.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/Cone.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/Cone.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/MExpr.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/MExpr.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/MExpr_rooted.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/MExpr_rooted.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/M_eq_solution.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/M_eq_solution.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/NExpr.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/NExpr.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/NExpr_rooted.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/NExpr_rooted.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/NStarExpr.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/NStarExpr.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/NStarExpr_rooted.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/NStarExpr_rooted.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/NStar_eq_solution.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/NStar_eq_solution.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/NStar_over_N_exists.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/NStar_over_N_exists.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/N_eq_solution.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/N_eq_solution.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/nil_mem_Cnat.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/nil_mem_Cnat.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise622/nil_mem_Cone.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise622/nil_mem_Cone.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/BasicInst28.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/BasicInst28.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Exp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/Exp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/ExpAlg.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/ExpAlg.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/ExpInitial.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/ExpInitial.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/ExpIso.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/ExpIso.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Exp_structure_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/Exp_structure_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Subsystemu2eproj_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/Subsystemu2eproj_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Texp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/Texp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/TexpF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/TexpF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Texp_rooted.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/Texp_rooted.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/algHom_ext.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/algHom_ext.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/algHom_fix.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/algHom_fix.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/algStr.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/algStr.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/algStr_strict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/algStr_strict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/comp_val.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/comp_val.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/constBot_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/constBot_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descAlgHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descAlgHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descComm.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descComm.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descDir.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descDir.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descDirLe.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descDirLe.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_eq_algHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descMap_eq_algHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_fix.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descMap_fix.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descMap_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_is_sup.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descMap_is_sup.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_le_algHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descMap_le_algHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descMap_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descRel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descRel_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel_le_algHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descRel_le_algHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel_le_succ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descRel_le_succ.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descRel_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel_succ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/descRel_succ.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/expHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expHom_comp_expInv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/expHom_comp_expInv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expHom_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/expHom_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expInv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/expInv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expInv_comp_expHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/expInv_comp_expHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expInv_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/expInv_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expInv_strict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/expInv_strict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expSub.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/expSub.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/ext.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/ext.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gBase.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gBase.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gChain.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gChain.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gColim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gColim.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gColim_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gColim_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gColim_obj_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gColim_obj_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gColim_obj_sys_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gColim_obj_sys_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFix.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gFix.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFix_fixed.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gFix_fixed.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFix_nil_mem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gFix_nil_mem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFix_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gFix_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFunctor.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gFunctor.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFunctorMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gFunctorMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFunctorMap_val.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gFunctorMap_val.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFunctor_obj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gFunctor_obj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gGen.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gGen.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gGen_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gGen_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gTower.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gTower_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gTower_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower_sub_colim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gTower_sub_colim.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower_succ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gTower_succ.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower_zero.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gTower_zero.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gcomp_rho_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gcomp_rho_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gcomp_rho_succ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gcomp_rho_succ.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gcomp_rho_zero.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/gcomp_rho_zero.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/iSupRho.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/iSupRho.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/iSupRho_eq_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/iSupRho_eq_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/id_val.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/id_val.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/inj_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/inj_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/isoOfObjEq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/isoOfObjEq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/isoOfObjEq_hom_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/isoOfObjEq_hom_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/isoOfObjEq_inv_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/isoOfObjEq_inv_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/key_rho.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/key_rho.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/map_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/map_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/map_proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/map_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/map_rho_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/map_rho_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/mem_gColim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/mem_gColim.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/oplusMapTok_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/oplusMapTok_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/oplusMapTok_proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/oplusMapTok_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/otimesMapTok_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/otimesMapTok_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/otimesMapTok_proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/otimesMapTok_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/prodMapTok_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/prodMapTok_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/prodMapTok_proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/prodMapTok_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/rho.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/rho.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/rho_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/rho_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/rho_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/rho_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/rho_zero_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/rho_zero_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/self_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/self_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/self_proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/self_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/sumMapTok_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/sumMapTok_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/sumMapTok_proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise623/sumMapTok_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Dsol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Dsol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Dsol_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Dsol_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Esol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Esol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Esol_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Esol_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Fsol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Fsol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/GammaD.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/GammaD.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/GammaE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/GammaE.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Gsol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Gsol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/exists_double_fixedPoint.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/exists_double_fixedPoint.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/exists_simultaneous_subsystems.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/exists_simultaneous_subsystems.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/fTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/fTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/fTok_GammaD_GammaE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/fTok_GammaD_GammaE.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/fTok_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/fTok_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/gTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/gTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/gTok_GammaD_GammaE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/gTok_GammaD_GammaE.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/gTok_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/gTok_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/master_Fsol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/master_Fsol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/master_Gsol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/master_Gsol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/mem_fTok_iUnion.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/mem_fTok_iUnion.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/mem_gTok_iUnion.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/mem_gTok_iUnion.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_GammaD.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_GammaD.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_GammaE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_GammaE.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_fTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_fTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_gTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_gTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/pIter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/pIter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/pIter_fst_subset_GammaD.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/pIter_fst_subset_GammaD.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/pIter_snd_subset_GammaE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/pIter_snd_subset_GammaE.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/galois.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/galois.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/inj_bounded.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/inj_bounded.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/inj_eq_sInf.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/inj_eq_sInf.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/inj_proj_apply_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/inj_proj_apply_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/inj_sSup.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/inj_sSup.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet_bounded.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet_bounded.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet_directed.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet_directed.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/mem_lowerSet.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/mem_lowerSet.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/proj_eq_sSup.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/proj_eq_sSup.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/proj_inj_apply.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/proj_inj_apply.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/upperSet.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/upperSet.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/upperSet_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/upperSet_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/embF_ne_liftTokMaster.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/embF_ne_liftTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/embF_subset_liftTokMaster.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/embF_subset_liftTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/eq_liftBot_or_exists_liftUp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/eq_liftBot_or_exists_liftUp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromLiftProd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/fromLiftProd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromLiftProd_mem_prod.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/fromLiftProd_mem_prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromLiftProd_toLiftProd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/fromLiftProd_toLiftProd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift_mem_embFF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift_mem_embFF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift_mem_embTF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift_mem_embTF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift_toSumLift.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift_toSumLift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/lift.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/lift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftBot.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftBot.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftBot_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftBot_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftBot_lt_liftUp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftBot_lt_liftUp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftProdEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftProdEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTokMaster.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTokMaster_inter_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftTokMaster_inter_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_mem_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_mem_embF_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_mem_embF_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_mem_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftUp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftUp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftUp_le_liftUp_iff.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftUp_le_liftUp_iff.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftUp_unlift.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/liftUp_unlift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/lift_oplus_lift_iso_sum.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/lift_oplus_lift_iso_sum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/lift_otimes_lift_iso_lift_prod.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/lift_otimes_lift_iso_lift_prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/lp_mem_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/lp_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/lp_prod_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/lp_prod_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/mem_liftBot.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/mem_liftBot.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/mem_liftUp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/mem_liftUp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/nil_mem_liftTokMaster.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/nil_mem_liftTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/o_embFF_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/o_embFF_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/o_embTF_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/o_embTF_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/o_mem_embFF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/o_mem_embFF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/o_mem_embTF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/o_mem_embTF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/ot_mem_prod.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/ot_mem_prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/ot_mem_prod_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/ot_mem_prod_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/sumLiftEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/sumLiftEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toLiftProd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/toLiftProd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toLiftProd_fromLiftProd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/toLiftProd_fromLiftProd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toLiftProd_mem_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/toLiftProd_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift_fromSumLift.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift_fromSumLift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift_mem_embF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift_mem_embT.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/unlift.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise626/unlift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/X_eq_master_of_embT_subset_leftN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/X_eq_master_of_embT_subset_leftN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/X_eq_master_of_nil_mem_leftN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/X_eq_master_of_nil_mem_leftN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/embF_subset_leftN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/embF_subset_leftN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/ext_of_principal.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/ext_of_principal.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/fstInj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/fstInj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/fstInj_comp_fstProj_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/fstInj_comp_fstProj_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/fstProj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/fstProj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/fstProj_comp_fstInj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/fstProj_comp_fstInj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/fst_trianglelefteq_prod.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/fst_trianglelefteq_prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/incl.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/incl.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/inclMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/inclMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/inclMap_comp_strctMap_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/inclMap_comp_strctMap_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/incl_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/incl_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/incl_strct_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/incl_strct_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/inlInj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/inlInj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/inlProj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/inlProj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/leftN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/leftN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/leftN_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/leftN_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/leftN_proper.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/leftN_proper.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/leftN_subset_iff.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/leftN_subset_iff.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/not_trianglelefteq_otimes.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/not_trianglelefteq_otimes.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/oplusTok_subsystem_sumTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/oplusTok_subsystem_sumTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/oplus_mem_leftN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/oplus_mem_leftN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/oplus_trianglelefteq_sum.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/oplus_trianglelefteq_sum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/otimesTok_subsystem_prodTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/otimesTok_subsystem_prodTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/otimes_trianglelefteq_prod.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/otimes_trianglelefteq_prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/otimes_unitPt_collapse.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/otimes_unitPt_collapse.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strct.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strct.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strctMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strctMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strctMap_comp_inclMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strctMap_comp_inclMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strct_incl.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strct_incl.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strct_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strct_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strictFun_trianglelefteq_funSpace.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strictFun_trianglelefteq_funSpace.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strictify.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strictify.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strictifyMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strictifyMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strictifyMap_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strictifyMap_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strictifyMap_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strictifyMap_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/strictifyMap_of_isStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/strictifyMap_of_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/subset_of_embF_subset_leftN.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/subset_of_embF_subset_leftN.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/subsingleton_element_of_only_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/subsingleton_element_of_only_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/toApproxMap_toFilter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/toApproxMap_toFilter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/toElementMap_inclMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/toElementMap_inclMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/toElementMap_strctMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/toElementMap_strctMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/toFilter_toApproxMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/toFilter_toApproxMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/toStrictFilter_toStrictMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/toStrictFilter_toStrictMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/toStrictMap_toStrictFilter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/toStrictMap_toStrictFilter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/twoPt.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/twoPt.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise627/unitPt.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise627/unitPt.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise628.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise628.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise628/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise628/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise628/IsFinite.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise628/IsFinite.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise628/Triangleleftequ2eelementEmbedding.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise628/Triangleleftequ2eelementEmbedding.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise628/finite_element_of_isFinite.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise628/finite_element_of_isFinite.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise628/isomorphic_of_finite_system.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise628/isomorphic_of_finite_system.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise628/isomorphic_of_trianglelefteq_both.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise628/isomorphic_of_trianglelefteq_both.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise628/orderIso_of_embeddings.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise628/orderIso_of_embeddings.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise628/projElementEmbedding.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise628/projElementEmbedding.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/FinSupp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/FinSupp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/fromPi.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/fromPi.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/fromPi_mem_slice.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/fromPi_mem_slice.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/fromPi_toPi.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/fromPi_toPi.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/index_of_some_mem_injI.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/index_of_some_mem_injI.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/injI.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/injI.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/injI_inter_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/injI_inter_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/injI_inter_same.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/injI_inter_same.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/injI_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/injI_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/injI_subset_iff.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/injI_subset_iff.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/injI_subset_sumMasterI.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/injI_subset_sumMasterI.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/inter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/ioplus.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/ioplus.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iotimes.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iotimes.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iotimes_only_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iotimes_only_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iotimes_subsingleton.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iotimes_subsingleton.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprod.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprodEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprodEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd_injective.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd_restrictTo_cons.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd_restrictTo_cons.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd_subset_iff.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd_subset_iff.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd_subset_slice.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprodNbhd_subset_slice.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprod_mem_iprodNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprod_mem_iprodNbhd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprod_mem_slice.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprod_mem_slice.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/iprod_mem_slice_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/iprod_mem_slice_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/isum.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/isum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/isum_summand_unique.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/isum_summand_unique.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/isum_trichotomy.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/isum_trichotomy.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/mem_iprodNbhd.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/mem_iprodNbhd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/none_mem_sumMasterI.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/none_mem_sumMasterI.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/none_not_mem_injI.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/none_not_mem_injI.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/proj_fromPi.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/proj_fromPi.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/restrictTo.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/restrictTo.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/slice.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/slice.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/slice_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/slice_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/slice_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/slice_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/slice_subset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/slice_subset.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/some_mem_injI.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/some_mem_injI.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/sumMasterI.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/sumMasterI.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/updTuple.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/updTuple.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/updTuple_apply_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/updTuple_apply_ne.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/updTuple_apply_self.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/updTuple_apply_self.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/z_mem_iprodNbhd_restrictTo.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/z_mem_iprodNbhd_restrictTo.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise629/z_mem_of_slices.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise629/z_mem_of_slices.lean)
- [NeighbourhoodSystems/DomainEquations/Gamma_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Gamma_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/IsInitial.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/IsInitial.lean)
- [NeighbourhoodSystems/DomainEquations/Iso.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Iso.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/Basic/notation4.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/Basic/notation4.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/Dprime.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/Dprime.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/Dprime_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/Dprime_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/IsGen.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/IsGen.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/Subsystemu2etrianglelefteq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/Subsystemu2etrianglelefteq.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/Trianglelefteq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/Trianglelefteq.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/dprimeEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/dprimeEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/isGen_exists.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/isGen_exists.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/isGen_fst_unique.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/isGen_fst_unique.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/isGen_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/isGen_inter.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/isGen_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/isGen_master.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/isGen_mono'.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/isGen_mono'.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/isGen_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/isGen_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/isGen_snd_unique.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/isGen_snd_unique.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/mem_Dprime.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/mem_Dprime.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/ofEl.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/ofEl.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/toEl.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/toEl.lean)
- [NeighbourhoodSystems/DomainEquations/Lemma615/trianglelefteq_of_projectionPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Lemma615/trianglelefteq_of_projectionPair.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition611.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition611.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition611Inst16.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition611Inst16.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/ProjectionPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/ProjectionPair.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/inj.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/inj_comp_proj_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/inj_comp_proj_le.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/inj_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/inj_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/proj.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/proj_comp_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/proj_comp_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/proj_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/proj_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/projectionPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/projectionPair.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/toElementMap_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/toElementMap_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/toElementMap_proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/toElementMap_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition66.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition66.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition66/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition66/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition66/comp_desc_eq_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition66/comp_desc_eq_id.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition66/initialIso.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition66/initialIso.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition66/iso_hom_unique.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition66/iso_hom_unique.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition67.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition67.lean)
- [NeighbourhoodSystems/DomainEquations/StrictDomainObj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/StrictDomainObj.lean)
- [NeighbourhoodSystems/DomainEquations/TAlgebra.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/TAlgebra.lean)
- [NeighbourhoodSystems/DomainEquations/Tc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Tc.lean)
- [NeighbourhoodSystems/DomainEquations/Tc_map_val.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Tc_map_val.lean)
- [NeighbourhoodSystems/DomainEquations/Tc_obj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Tc_obj.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Dceq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Dceq.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Dchain.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Dchain.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Dsys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Dsys.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Dsys_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Dsys_master.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Dsys_sub_Tcolim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Dsys_sub_Tcolim.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Dsys_sub_colim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Dsys_sub_colim.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Dsys_succ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Dsys_succ.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Setup.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Setup.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Tcolim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Tcolim.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Tcolim_eq_colim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Tcolim_eq_colim.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Tcolim_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Tcolim_master.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/Tcolim_sub_colim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/Tcolim_sub_colim.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/algHom_ext.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/algHom_ext.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/algHom_unique.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/algHom_unique.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/cat_comp_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/cat_comp_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/chain_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/chain_le.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/colim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/colim.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/colimCeq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/colimCeq.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/colimIso.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/colimIso.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/colimObj_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/colimObj_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/colim_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/colim_master.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/colim_sub_Tcolim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/colim_sub_Tcolim.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/domainObj_ext.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/domainObj_ext.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/exists_algebra_with_hom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/exists_algebra_with_hom.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/exists_unique_strict_algHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/exists_unique_strict_algHom.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/gcomp_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/gcomp_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/gcomp_rho_indep.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/gcomp_rho_indep.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/gcomp_rho_succ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/gcomp_rho_succ.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/gcomp_rho_zero_indep.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/gcomp_rho_zero_indep.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/gcomp_rho_zero_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/gcomp_rho_zero_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/iSupRho.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/iSupRho.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/iSupRho_eq_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/iSupRho_eq_id.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/isoOfEq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/isoOfEq.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/isoOfEq_conj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/isoOfEq_conj.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/iter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/iter.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/key_rho.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/key_rho.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/map_comp_proj_heq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/map_comp_proj_heq.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/map_rho_heq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/map_rho_heq.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/mem_cast.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/mem_cast.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/mem_colim.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/mem_colim.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/nonempty_algHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/nonempty_algHom.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/nonempty_strict_algHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/nonempty_strict_algHom.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/rec_trans.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/rec_trans.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/rho.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/rho.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/rho_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/rho_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/rho_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/rho_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/rho_zero_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/rho_zero_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/set_rec_trans.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/set_rec_trans.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/strict_rel_master.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/strict_rel_master.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/subsystem_cast.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/subsystem_cast.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem614/transport_heq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem614/transport_heq.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem616.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem616.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem616/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem616/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem616/botStrict_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem616/botStrict_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem616/opStep.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem616/opStep.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem616/trianglelefteq_of_isInitial.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem616/trianglelefteq_of_isInitial.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/comp_mono_gen.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/comp_mono_gen.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/homOp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/homOp.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/homOpComp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/homOpComp.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/homOpComp_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/homOpComp_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/homOp_apply_filter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/homOp_apply_filter.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/homOp_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/homOp_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/isStrict_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/isStrict_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/isStrict_of_comp_eq_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/isStrict_of_comp_eq_id.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/nonempty_algHom_of_continuousOnMaps.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/nonempty_algHom_of_continuousOnMaps.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/toStrictFilter_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/toStrictFilter_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/toStrictFilter_toStrictMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/toStrictFilter_toStrictMap.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/toStrictMap_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Theorem69/toStrictMap_mono.lean)
- [NeighbourhoodSystems/DomainEquations/cStr.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/cStr.lean)
- [NeighbourhoodSystems/DomainEquations/ccEquiv_apply.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/ccEquiv_apply.lean)
- [NeighbourhoodSystems/DomainEquations/ccEquiv_comp_symm.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/ccEquiv_comp_symm.lean)
- [NeighbourhoodSystems/DomainEquations/ccEquiv_symm_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/ccEquiv_symm_comp.lean)
- [NeighbourhoodSystems/DomainEquations/chain_le_of_succ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/chain_le_of_succ.lean)
- [NeighbourhoodSystems/DomainEquations/comm_unique.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/comm_unique.lean)
- [NeighbourhoodSystems/DomainEquations/comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/comp.lean)
- [NeighbourhoodSystems/DomainEquations/compAfter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/compAfter.lean)
- [NeighbourhoodSystems/DomainEquations/comp_val.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/comp_val.lean)
- [NeighbourhoodSystems/DomainEquations/component_bot.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/component_bot.lean)
- [NeighbourhoodSystems/DomainEquations/consMap_mem_embBit.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/consMap_mem_embBit.lean)
- [NeighbourhoodSystems/DomainEquations/consMap_not_mem_embBit_ne.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/consMap_not_mem_embBit_ne.lean)
- [NeighbourhoodSystems/DomainEquations/consMap_not_mem_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/consMap_not_mem_nil.lean)
- [NeighbourhoodSystems/DomainEquations/consSeq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/consSeq.lean)
- [NeighbourhoodSystems/DomainEquations/consSeq_succ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/consSeq_succ.lean)
- [NeighbourhoodSystems/DomainEquations/consSeq_zero.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/consSeq_zero.lean)
- [NeighbourhoodSystems/DomainEquations/constBot_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/constBot_le.lean)
- [NeighbourhoodSystems/DomainEquations/descAlgHom_uniq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descAlgHom_uniq.lean)
- [NeighbourhoodSystems/DomainEquations/descComm.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descComm.lean)
- [NeighbourhoodSystems/DomainEquations/descE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descE.lean)
- [NeighbourhoodSystems/DomainEquations/descF.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descF.lean)
- [NeighbourhoodSystems/DomainEquations/descF_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descF_mono.lean)
- [NeighbourhoodSystems/DomainEquations/descMap_comm.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descMap_comm.lean)
- [NeighbourhoodSystems/DomainEquations/descMap_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descMap_eq.lean)
- [NeighbourhoodSystems/DomainEquations/descMap_fix.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descMap_fix.lean)
- [NeighbourhoodSystems/DomainEquations/descMap_hcone.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descMap_hcone.lean)
- [NeighbourhoodSystems/DomainEquations/descMap_hsing.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descMap_hsing.lean)
- [NeighbourhoodSystems/DomainEquations/descMap_satisfiesRec.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descMap_satisfiesRec.lean)
- [NeighbourhoodSystems/DomainEquations/descMap_strBot.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descMap_strBot.lean)
- [NeighbourhoodSystems/DomainEquations/descMap_strElem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descMap_strElem.lean)
- [NeighbourhoodSystems/DomainEquations/descMap_strict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descMap_strict.lean)
- [NeighbourhoodSystems/DomainEquations/descMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descMap_toElementMap.lean)
- [NeighbourhoodSystems/DomainEquations/descOp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descOp.lean)
- [NeighbourhoodSystems/DomainEquations/descOp_apply.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descOp_apply.lean)
- [NeighbourhoodSystems/DomainEquations/descOp_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descOp_mono.lean)
- [NeighbourhoodSystems/DomainEquations/descSeq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descSeq.lean)
- [NeighbourhoodSystems/DomainEquations/descSeqEltMono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descSeqEltMono.lean)
- [NeighbourhoodSystems/DomainEquations/descSeq_dir.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descSeq_dir.lean)
- [NeighbourhoodSystems/DomainEquations/descSeq_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descSeq_mono.lean)
- [NeighbourhoodSystems/DomainEquations/descSeq_mono_succ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descSeq_mono_succ.lean)
- [NeighbourhoodSystems/DomainEquations/descSeq_strict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descSeq_strict.lean)
- [NeighbourhoodSystems/DomainEquations/descStrict.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descStrict.lean)
- [NeighbourhoodSystems/DomainEquations/descVal.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descVal.lean)
- [NeighbourhoodSystems/DomainEquations/descVal_append.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descVal_append.lean)
- [NeighbourhoodSystems/DomainEquations/descVal_mono_z.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/descVal_mono_z.lean)
- [NeighbourhoodSystems/DomainEquations/dsharpEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/dsharpEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/embPair_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embPair_injective.lean)
- [NeighbourhoodSystems/DomainEquations/embPair_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embPair_inter.lean)
- [NeighbourhoodSystems/DomainEquations/embPair_ne_Gamma.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embPair_ne_Gamma.lean)
- [NeighbourhoodSystems/DomainEquations/embPair_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embPair_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/embPair_subset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embPair_subset.lean)
- [NeighbourhoodSystems/DomainEquations/embPair_subset_Gamma.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embPair_subset_Gamma.lean)
- [NeighbourhoodSystems/DomainEquations/embZero_injective.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embZero_injective.lean)
- [NeighbourhoodSystems/DomainEquations/embZero_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embZero_inter.lean)
- [NeighbourhoodSystems/DomainEquations/embZero_inter_embPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embZero_inter_embPair.lean)
- [NeighbourhoodSystems/DomainEquations/embZero_ne_Gamma.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embZero_ne_Gamma.lean)
- [NeighbourhoodSystems/DomainEquations/embZero_ne_embPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embZero_ne_embPair.lean)
- [NeighbourhoodSystems/DomainEquations/embZero_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embZero_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/embZero_subset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embZero_subset.lean)
- [NeighbourhoodSystems/DomainEquations/embZero_subset_Gamma.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/embZero_subset_Gamma.lean)
- [NeighbourhoodSystems/DomainEquations/fromS.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/fromS.lean)
- [NeighbourhoodSystems/DomainEquations/fromS_mem_embPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/fromS_mem_embPair.lean)
- [NeighbourhoodSystems/DomainEquations/fromS_mem_embZero.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/fromS_mem_embZero.lean)
- [NeighbourhoodSystems/DomainEquations/fromS_toS.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/fromS_toS.lean)
- [NeighbourhoodSystems/DomainEquations/gcomp_rho_succ.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/gcomp_rho_succ.lean)
- [NeighbourhoodSystems/DomainEquations/gcomp_rho_zero.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/gcomp_rho_zero.lean)
- [NeighbourhoodSystems/DomainEquations/genKey.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/genKey.lean)
- [NeighbourhoodSystems/DomainEquations/genKey0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/genKey0.lean)
- [NeighbourhoodSystems/DomainEquations/genKeyBot.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/genKeyBot.lean)
- [NeighbourhoodSystems/DomainEquations/iSupRho_eq_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/iSupRho_eq_id.lean)
- [NeighbourhoodSystems/DomainEquations/id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/id.lean)
- [NeighbourhoodSystems/DomainEquations/id_val.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/id_val.lean)
- [NeighbourhoodSystems/DomainEquations/imap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/imap.lean)
- [NeighbourhoodSystems/DomainEquations/inSharp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/inSharp.lean)
- [NeighbourhoodSystems/DomainEquations/interSys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/interSys.lean)
- [NeighbourhoodSystems/DomainEquations/interSys_nbset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/interSys_nbset.lean)
- [NeighbourhoodSystems/DomainEquations/interSys_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/interSys_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/isStrict_imap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/isStrict_imap.lean)
- [NeighbourhoodSystems/DomainEquations/isStrict_ofIso.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/isStrict_ofIso.lean)
- [NeighbourhoodSystems/DomainEquations/isStrict_prodMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/isStrict_prodMap.lean)
- [NeighbourhoodSystems/DomainEquations/isStrict_sumMap3.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/isStrict_sumMap3.lean)
- [NeighbourhoodSystems/DomainEquations/iterAlg.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/iterAlg.lean)
- [NeighbourhoodSystems/DomainEquations/iterBot_eq.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/iterBot_eq.lean)
- [NeighbourhoodSystems/DomainEquations/iterIsInitial.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/iterIsInitial.lean)
- [NeighbourhoodSystems/DomainEquations/iterObj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/iterObj.lean)
- [NeighbourhoodSystems/DomainEquations/iterProdIso_apply.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/iterProdIso_apply.lean)
- [NeighbourhoodSystems/DomainEquations/iterProdIso_symm_pair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/iterProdIso_symm_pair.lean)
- [NeighbourhoodSystems/DomainEquations/iterSys_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/iterSys_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/jmap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/jmap.lean)
- [NeighbourhoodSystems/DomainEquations/jmap_comp_imap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/jmap_comp_imap.lean)
- [NeighbourhoodSystems/DomainEquations/kHead.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/kHead.lean)
- [NeighbourhoodSystems/DomainEquations/kHead_apply.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/kHead_apply.lean)
- [NeighbourhoodSystems/DomainEquations/lambek.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/lambek.lean)
- [NeighbourhoodSystems/DomainEquations/memS_embPair_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/memS_embPair_inv.lean)
- [NeighbourhoodSystems/DomainEquations/memS_embZero_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/memS_embZero_inv.lean)
- [NeighbourhoodSystems/DomainEquations/memS_inter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/memS_inter.lean)
- [NeighbourhoodSystems/DomainEquations/memS_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/memS_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/memS_subset_gamma.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/memS_subset_gamma.lean)
- [NeighbourhoodSystems/DomainEquations/mem_Gamma.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/mem_Gamma.lean)
- [NeighbourhoodSystems/DomainEquations/mem_embL.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/mem_embL.lean)
- [NeighbourhoodSystems/DomainEquations/mem_embPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/mem_embPair.lean)
- [NeighbourhoodSystems/DomainEquations/mem_embR.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/mem_embR.lean)
- [NeighbourhoodSystems/DomainEquations/mem_embZero.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/mem_embZero.lean)
- [NeighbourhoodSystems/DomainEquations/mem_subset_j0_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/mem_subset_j0_inv.lean)
- [NeighbourhoodSystems/DomainEquations/mem_subset_j1_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/mem_subset_j1_inv.lean)
- [NeighbourhoodSystems/DomainEquations/mem_subset_j2_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/mem_subset_j2_inv.lean)
- [NeighbourhoodSystems/DomainEquations/ofMem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/ofMem.lean)
- [NeighbourhoodSystems/DomainEquations/ofMem_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/ofMem_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/pairSharp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/pairSharp.lean)
- [NeighbourhoodSystems/DomainEquations/pair_bot.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/pair_bot.lean)
- [NeighbourhoodSystems/DomainEquations/prodFunctor.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/prodFunctor.lean)
- [NeighbourhoodSystems/DomainEquations/prodMapHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/prodMapHom.lean)
- [NeighbourhoodSystems/DomainEquations/prodMap_idMap_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/prodMap_idMap_mono.lean)
- [NeighbourhoodSystems/DomainEquations/prodObj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/prodObj.lean)
- [NeighbourhoodSystems/DomainEquations/prod_dsharp_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/prod_dsharp_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/prod_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/prod_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/rec_determines.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/rec_determines.lean)
- [NeighbourhoodSystems/DomainEquations/rho_apply.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/rho_apply.lean)
- [NeighbourhoodSystems/DomainEquations/sinj0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sinj0.lean)
- [NeighbourhoodSystems/DomainEquations/sinj0_mem_j0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sinj0_mem_j0.lean)
- [NeighbourhoodSystems/DomainEquations/sinj1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sinj1.lean)
- [NeighbourhoodSystems/DomainEquations/sinj1_mem_j1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sinj1_mem_j1.lean)
- [NeighbourhoodSystems/DomainEquations/sinj1_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sinj1_mono.lean)
- [NeighbourhoodSystems/DomainEquations/sinj2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sinj2.lean)
- [NeighbourhoodSystems/DomainEquations/sinj2_mem_j2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sinj2_mem_j2.lean)
- [NeighbourhoodSystems/DomainEquations/sinj2_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sinj2_mono.lean)
- [NeighbourhoodSystems/DomainEquations/strHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/strHom.lean)
- [NeighbourhoodSystems/DomainEquations/str_comp_desc.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/str_comp_desc.lean)
- [NeighbourhoodSystems/DomainEquations/subFam.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/subFam.lean)
- [NeighbourhoodSystems/DomainEquations/subFam_inter_closed.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/subFam_inter_closed.lean)
- [NeighbourhoodSystems/DomainEquations/subFam_master_mem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/subFam_master_mem.lean)
- [NeighbourhoodSystems/DomainEquations/subFam_mem_E.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/subFam_mem_E.lean)
- [NeighbourhoodSystems/DomainEquations/subFam_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/subFam_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/subFam_sInter_mem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/subFam_sInter_mem.lean)
- [NeighbourhoodSystems/DomainEquations/subFam_sUnion_mem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/subFam_sUnion_mem.lean)
- [NeighbourhoodSystems/DomainEquations/subIso.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/subIso.lean)
- [NeighbourhoodSystems/DomainEquations/subsystemReprIso.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/subsystemReprIso.lean)
- [NeighbourhoodSystems/DomainEquations/succChainDir.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/succChainDir.lean)
- [NeighbourhoodSystems/DomainEquations/sum3_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sum3_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/sumMap3.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sumMap3.lean)
- [NeighbourhoodSystems/DomainEquations/sumMap3_comp.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sumMap3_comp.lean)
- [NeighbourhoodSystems/DomainEquations/sumMap3_id.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sumMap3_id.lean)
- [NeighbourhoodSystems/DomainEquations/sumMap3_sinj0.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sumMap3_sinj0.lean)
- [NeighbourhoodSystems/DomainEquations/sumMap3_sinj1.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sumMap3_sinj1.lean)
- [NeighbourhoodSystems/DomainEquations/sumMap3_sinj2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sumMap3_sinj2.lean)
- [NeighbourhoodSystems/DomainEquations/sumSys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sumSys.lean)
- [NeighbourhoodSystems/DomainEquations/sumSys_mem_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sumSys_mem_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/sum_mem_inj₀_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sum_mem_inj₀_inv.lean)
- [NeighbourhoodSystems/DomainEquations/sum_mem_inj₁_inv.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/sum_mem_inj₁_inv.lean)
- [NeighbourhoodSystems/DomainEquations/tStr.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/tStr.lean)
- [NeighbourhoodSystems/DomainEquations/tcMapHom.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/tcMapHom.lean)
- [NeighbourhoodSystems/DomainEquations/tcObj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/tcObj.lean)
- [NeighbourhoodSystems/DomainEquations/tcObj_sys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/tcObj_sys.lean)
- [NeighbourhoodSystems/DomainEquations/toCC_consMap.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/toCC_consMap.lean)
- [NeighbourhoodSystems/DomainEquations/toCC_strElem_nil.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/toCC_strElem_nil.lean)
- [NeighbourhoodSystems/DomainEquations/toElementMap_le_of_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/toElementMap_le_of_le.lean)
- [NeighbourhoodSystems/DomainEquations/toS.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/toS.lean)
- [NeighbourhoodSystems/DomainEquations/toS_fromS.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/toS_fromS.lean)
- [NeighbourhoodSystems/DomainEquations/toS_mem_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/toS_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainEquations/toS_mem_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/toS_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainEquations/unionSys.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/unionSys.lean)
- [NeighbourhoodSystems/DomainEquations/unionSys_nbset.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/unionSys_nbset.lean)
- [NeighbourhoodSystems/DomainEquations/unionSys_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/unionSys_subsystem.lean)
