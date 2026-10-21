# Example 6.1

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

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/Example61.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/Gamma.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/Gamma.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/MemS.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/MemS.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/embL.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/embL.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/embPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/embPair.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/embR.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/embR.lean)
- [NeighbourhoodSystems/DomainEquations/Example61/embZero.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example61/embZero.lean)
