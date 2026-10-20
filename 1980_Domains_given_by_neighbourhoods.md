# Domains given by neighbourhoods

Often an object (or element) can be determined by a selection of its properties. Often it is also the case that it is easier (more convenient, more elementary) to think of these properties than it is to think of the elements themselves. Let us term the properties under consideration *neighbourhoods*, the family of those allowed a *neighbourhood system*.

Generally, the collection of these neighbourhoods is, for one reason or another, somewhat restricted; that is, a completely arbitrary property may not be allowable as a neighbourhood. Therefore, the elements determined by selections of neighbourhoods may not be as separable into the discrete objects common to the classical view of set theory. This is particularly true in working with infinite objects: it is hard to specify an infinite element completely. The theory of elements to be studied here, then, is going to permit *partial elements* as well as *total elements*, and each neighbourhood system will define a *domain* of such elements.

Since we may wish to use a neighbourhood system to introduce elements not previously investigated, the neighbourhoods do not have to be regarded as sets of the as-yet-to-be-defined objects. We can take a non-empty set $\Delta$ of *tokens* (or "traces") that function as "parts" of elements — or even as parts of "descriptions" of elements. Then a neighbourhood is a subset $X \subseteq \Delta$ containing all those tokens that provide sufficient information when taken together to "approximate" a possible element up to a certain "degree". All these words in inverted commas are vague, and in any case we shall have at the start only a *qualitative* theory of "degree of approximation". A token should be considered as a very "rough" representative of an element, and a neighbourhood should be regarded as "smoothing out" irrelevant details by grouping together *all* those representatives sharing some common feature. One neighbourhood, then,
may be only a very incomplete specification of an (ideal) element; fuller specifications can be secured by taking "convergent" sequences of neighbourhoods. Even then convergence need not be to a total element.

Let us call the family of allowed neighbourhoods $\mathcal{D}$; it is a family of subsets of the set $\Delta$. An obvious first question is: when are two neighbourhoods $X$, $Y \in \mathcal{D}$ neighbourhoods of the "same" element? This question of course generalizes to a (finite) sequence of neighbourhoods. This property we will call the *consistency* of the sequence of neighbourhoods. By definition this will mean that the given neighbourhoods all contain a common neighbourhood in $\mathcal{D}$. That is, for $X$, $Y$ to be consistent, there must be a $Z \in \mathcal{D}$ with $Z \subseteq X$ and $Z \subseteq Y$. This is not a very informative definition, but it has something of the flavour of a notion of consistency insofar as it can be expressed within $\mathcal{D}$. When consistency holds it seems reasonable enough at first glance to say that the intersection $X \cap Y$ is also an approximation to this common element. If this is reasonable, then $X \cap Y$ should also be regarded as a neighbourhood. This assumption has many consequences, but as a preliminary theory of approximation we will find it quite workable with many natural instances. Taking intersections just means taking more and more properties of the element and putting them together "conjunctively". It is something we do all the time. We therefore accept the idea for the present for giving our first principal definition.

DEFINITION 1.1. A family $\mathcal{D}$ of subsets of a given set $\Delta$ is called a *neighbourhood system* (over $\Delta$) iff it is a non-empty family closed under the intersection of finite consistent sequences of neighbourhoods. That is to say, $\mathcal{D}$ must fulfill these two conditions:

(i) $\Delta \in \mathcal{D}$;

(ii) whenever $X$, $Y$, $Z \in \mathcal{D}$ and $Z \subseteq X \cap Y$, then $X \cap Y \in \mathcal{D}$. $\square$
We remark that by convention $\Delta$ corresponds to the intersection of an empty sequence of neighbourhoods; in particular,

$$
\bigcap_{i < n} X_i = \Delta, \text{ if } n = 0;
$$

$$
= \left(\bigcap_{i < n-1} X_i\right) \cap X_{n-1}, \text{ if } n > 0.
$$

Of course, from (ii), we can extend the intersection property to any finite sequence. Consequently, we can say $X_0, \dots, X_{n-1}$ is consistent in $\mathcal{D}$ iff

$$
\bigcap_{i < n} X_i \in \mathcal{D}.
$$

Some examples will help us understand the notions better.

EXAMPLE 1.2. Let $\Delta = \{0, 1\}$ and let $\mathcal{D} = \{\{0, 1\}, \{0\}, \{1\}\}$.

In pictures we have:

```
╭──────────────────────────╮
│   ╭───╮       ╭───╮      │
│   │ 0 │       │ 1 │      │
│   ╰───╯       ╰───╯      │
╰──────────────────────────╯
```

The intention is that 0 and 1 can be completely specified and that they can be identified with the total elements. As we shall see, there is only one partial element: either we give no information (the neighbourhood $\{0, 1\}$), or we decide between 0 and 1 (by giving $\{0\}$ or $\{1\}$). $\square$

EXAMPLE 1.3. Let $\Delta = \{0, 1, 2\}$ and let $\mathcal{D} = \{\{0, 1, 2\}, \{1, 2\}, \{2\}\}$.

In pictures we have:

```
╭──────────────────────────────────────╮
│  0   ╭──────────────────────╮        │
│      │  1        ╭───╮       │        │
│      │           │ 2 │       │        │
│      │           ╰───╯       │        │
│      ╰──────────────────────╯        │
╰──────────────────────────────────────╯
Instead of stepping to the total element (here represented by 2) in one big step, the passage is divided into two steps. (Note 0 and 1 cannot be taken as representing total elements.) This example is not very interesting because the direction of approximation is unique. We need an example with some choice. $\square$

EXAMPLE 1.4. Let $\Delta = \{\Lambda, 0, 1, 00, 01, 10, 11\}$ and let $\mathcal{D} = \{\Delta, \{0, 00, 01\}, \{1, 10, 11\}, \{00\}, \{01\}, \{10\}, \{11\}\}$.

Or more understandably in pictures:

```
╭──────────────────────────────────────────────────────────────╮
│   ╭───╮      ╭───╮      ╭───╮      ╭───╮                     │
│   │00 │      │01 │      │10 │      │11 │                     │
│   ╰───╯      ╰───╯      ╰───╯      ╰───╯                     │
│     ╭──────────────────╮    ╭──────────────────╮             │
│     │ 0    00     01   │    │ 1    10     11   │             │
│     ╰──────────────────╯    ╰──────────────────╯             │
│          ╭──────────╮              ╭──────────╮              │
│          │    0     │              │    1     │              │
│          ╰──────────╯              ╰──────────╯              │
│                 ╭──────────────────────────╮                 │
│                 │            Λ             │                 │
│                 ╰──────────────────────────╯                 │
╰──────────────────────────────────────────────────────────────╯
```

The tokens are finite sequences of 0's and 1's (up to length 2) with $\Lambda$ the empty sequence; they form — in the picture — the binary tree with the sequences as the nodes. The neighbourhoods are the subtrees of all nodes above a given node. Obviously this can be generalized to sequences of any length (and to trees less regular than the binary tree). The total elements of the example correspond to the top nodes 00, 01, 10, 11 and the lower nodes to the partial elements. When we are not at a top node we have only partially determined a sequence, and the branching indicates that we have some choice as to how the sequence can be extended. $\square$

It should be noted that, in these three examples, the reason that we have a neighbourhood system is a simple consequence of a

**Resolutions from the image:** “is unique” (not “in unique”); $\mathcal{D}$ begins with $\Delta$, not $\Lambda$; Pass 1’s nested-box diagram matches the neighborhood boundaries in the scan; em dashes around “in the picture” as in the source.
very special circumstance: in these systems two neighbourhoods are either disjoint or one is included in the other. This arrangement of neighbourhoods is by no means necessary.

EXAMPLE 1.5. Let $\Delta = \{0, 1, 2, 3\}$ and let $\mathcal{D}$ be the family of all non-empty subsets of $\Delta$.

This system is a direct generalization of Example 1.2., which was special owing to the small number of tokens. (The other examples were special by virtue of the choice of neighbourhoods.) The verification that the present $\mathcal{D}$ is a neighbourhood system rests on nothing more than the remark that sets are consistent in $\mathcal{D}$ iff they have a non-empty intersection. Clearly the arrangement of neighbourhoods in $\mathcal{D}$ can be as varied as a four-element set will allow; if $\Delta$ were made larger, the possible combinations of neighbourhoods could be made as complex as you wish. $\square$

Having some idea now of the variety of neighbourhood systems, we have to discuss what it is they do. As stressed before, the tokens do not have to correspond directly to the elements; but where, we ask, do the elements come from? One obvious suggestion for determining an element is to produce a sequence of "better and better" neighbourhoods:

$$
X_0 \supseteq X_1 \supseteq \cdots \supseteq X_n \supseteq \cdots
$$

Trivially, any finite initial segment of this sequence is consistent, and so each $X_n$ is a partial approximation to the "limit". If $\mathcal{D}$ were always to be taken as *finite*, of course, there would be no point in discussing limits since any such sequence would eventually be constant. The elements in the finite case would therefore be completely represented by neighbourhoods with the *minimal* neighbourhoods corresponding to the total elements. But there are many reasons to go beyond the finite (though perhaps not too far beyond).

Suppose $\langle Y_n \rangle_{n=0}^\infty$ is another "convergent" sequence with
$Y_{n+1} \subseteq Y_n$ for all indices: when do the two sequences of neighbourhoods determine the *same limit*? The two sequences can surely be different; for example, $\langle Y_n \rangle_{n=0}^\infty$ could be a subsequence of $\langle X_n \rangle_{n=0}^\infty$, say, $Y_n = X_{2n}$. Still we would want to say that the same limit is obtained. Without being given any further structure on the neighbourhoods, a simple answer is just to say that each sequence goes *equally deep* as the other:

for each $m$ there is an $n$ with $X_n \subseteq Y_m$, and

for each $n$ there is an $m$ with $Y_m \subseteq X_n$.

This definition obviously puts sequences into equivalence classes, and so elements could be identified with these. But such a definition is clumsy for two reasons: it is always tiresome to work with equivalence classes, and there is no reason to think that simple infinite sequences are adequate for determining elements without some rather drastic assumptions on $\mathcal{D}$. Nevertheless, the idea is *suggestive*; we just have to find some construct to represent elements in a unique way and to phrase it in a general enough manner.

Start with $\langle X_n \rangle_{n=0}^\infty$ again, which "converges" as before. Think of all the other sequences equivalent to this one in the sense just defined. We can define the class of all terms of all such sequences very easily as being the family:

$$
x = \{Z \in \mathcal{D} \mid X_n \subseteq Z \text{ for some } n\}.
$$

It is easy to prove that if we form the analogous class for $\langle Y_n \rangle_{n=0}^\infty$, then the two families are *equal* if and only if the sequences are *equivalent*. Thus, we seem justified in letting $x$ represent the limit of $\langle X_n \rangle_{n=0}^\infty$. All we have to do now is to remark on what sort of class $x$ is as a subfamily of $\mathcal{D}$; what we abstract from the construction, however, will be just a bit more general than taking those $x$ that result from sequences.

DEFINITION 1.6. The (ideal) elements of a neighbourhood system $\mathcal{D}$ are those subfamilies $x \subseteq \mathcal{D}$ where:

(i) $\Delta \in x$;

(ii) $X, Y \in x$ always implies $X \cap Y \in x$; and

(iii) whenever $X \in x$ and $X \subseteq Y \in \mathcal{D}$, then $Y \in x$.

The *domain* of all such elements is written as $|\mathcal{D}|$. $\square$
The idea of 1.6 is a well-known mathematical device: the families $x$ satisfying (i)–(iii) are usually called *filters*. Most frequently the emphasis is put on the *maximal* filters, and these would be our *total* elements; however, in general, the proof that maximal filters exist is non-constructive, so for our purposes it is better not to neglect the partial filters. When maximal filters can be found, well and good, but we do not have to insist on them. Note that the generality of 1.6 is achieved by not requiring that there is a sequence of neighbourhoods that "generates" the filter $x$. (See Exercise 1.22.)

We have often said that neighbourhoods determine partial elements by themselves; we now make this remark precise.

DEFINITION 1.7. For $X \in \mathcal{D}$, the *principal filter* determined by $X$ is defined by:

$$
\uparrow X = \{ Y \in \mathcal{D} \mid X \subseteq Y \}.
$$

The principal filters form what we shall call the *finite elements* of the domain $|\mathcal{D}|$. $\square$

It is obvious that the correspondence between $X$ and $\uparrow X$ is one-one and inclusion *reversing*, in the sense that

$$
X \subseteq Y \quad \text{iff} \quad \uparrow Y \subseteq \uparrow X
$$

for all $X, Y \in \mathcal{D}$. But, except in very special cases, there is much more to $|\mathcal{D}|$ than just the finite elements. Much of our investigation will be concerned with finding out how much more. The finite elements are, in a certain sense, "dense" in $|\mathcal{D}|$, however, because it is also obvious from the definitions that for each $x \in |\mathcal{D}|$

$$
x = \bigcup \{ \uparrow X \mid X \in x \}.
$$

That is, every element is a certain type of "limit" of finite elements. (This statement is made more precise in Exercise 1.21)

We note that we have now had several occasions to use inclusion relationships between elements; this is an important relationship, and we give it a special name.
DEFINITION 1.8. For $x, y \in |\mathcal{D}|$, we say that $x$ *approximates* $y$ iff $x \subseteq y$. The element that approximates all others, $\{\Delta\}$, is called $\perp$ (read: *bottom*); it is the "least defined" element, or the "most partial" element. Elements maximal with respect to the approximation relation are called *total elements*. $\square$

EXAMPLES 1.2 – 1.5 (Revisited). The examples as given were all finite, so any explicitly given filter $x$ is principal, the element is finite, the minimal $X \in x$ tells us all we need to know. In such simple situations there is essentially no difference between elements and neighbourhoods — except for the reversal of the order as noted. This (necessary) reversal should not, however, become a matter of confusion: the smaller the neighbourhood has become, the more it has "converged", and so the better defined the element has become. In the approximation relation the "poorer" elements are placed below the "better" with the total up at the top. This will become clearer in discussing "infinite" elements.

Example 1.3 will be generalized in Exercise 1.12. Let us here generalize first 1.4. We let

$$
\Delta = \Sigma^*,
$$

where $\Sigma = \{0, 1\}$ and $\Sigma^*$ means the set of all finite sequences of 0's and 1's, with $\Lambda$ being the empty sequence. We write $\sigma\tau$ for the *concatenation* or *juxtaposition* of two sequences $\sigma, \tau \in \Sigma^*$. Define

$$
B = \{\sigma\Sigma^* \mid \sigma \in \Sigma^*\}, \text{ where}
$$

$$
\sigma X = \{\sigma\tau \mid \tau \in X\},
$$

for an arbitrary set $X \subseteq \Sigma^*$. In other words, a neighbourhood in $B$ consists of all *extensions* of a given sequence $\sigma$. (Refer back to the finite version of 1.4.) We use the letter "B" to remind us of "binary", and this is an example we shall refer to many times. The proof (if it is not obvious) that $B$ is a neighbourhood system should be done as an exercise.

What do we find in $|B|$? Of course $\perp = \{\Delta\} \in |B|$. For any $x \in |B|$ and $\sigma \in \Sigma^*$ define

$$
\sigma x = \{Y \mid \sigma X \subseteq Y \text{ some } X \in x\}.
$$
Again there is an exercise here to show $\sigma x \in |B|$. In particular $\sigma\perp \in |B|$ for all $\sigma \in \Sigma^*$, and these are just the finite elements. The minimal element of $\sigma\perp$ is $\sigma\Delta$. Note that $\sigma_0\perp \subseteq \sigma_1\perp$ if and only if $\sigma_0$ is an *initial segment* of the sequence $\sigma_1$.

If now $x \in |B|$ is any explicitly given element (that is, if we know for any $X \in B$ whether or not $X \in x$), we have but to work out from these definitions that

$$
x = \bigcup_{n=0}^{\infty} \sigma_n\perp,
$$

where the $\sigma_n \in \Sigma^*$ and each $\sigma_n$ is an initial segment of the next $\sigma_{n+1}$. *In general, in any domain, an element is uniquely determined by its finite approximations, and we are just making this explicit in $|B|$.* When we have complete knowledge of $x$, then there are two cases: either the approximations $\sigma_n\perp$ become constant from some point on (where $n > n_0$), or not. In the first case $x$ is finite and equal to $\sigma_{n_0}\perp$; in the second case $x$ is infinite and the $\sigma_n$ fill out an infinite (one-way) sequence.

The generalization of 1.5 to the infinite case where $\Delta = \mathbf{N} = \{0, 1, 2, 3, \ldots, n, \ldots\}$ can be made in more than one way: for instance either we use as neighbourhoods *all* non-empty subsets of $\Delta$ or just those omitting but a finite number of integers. And, as will become apparent, there are other choices giving domains of quite different characters. $\square$

Many constructions (choices of $\mathcal{D}$) lead to the "same" domain; "sameness" is an important notion and it is to be defined in terms of "isomorphism", which in turn is to be defined in terms of approximation preserving correspondences.

DEFINITION 1.9. Two neighbourhood systems $\mathcal{D}_0$ and $\mathcal{D}_1$ determine *isomorphic domains* iff there is a one-one correspondence between $|\mathcal{D}_0|$ and $|\mathcal{D}_1|$ which preserves inclusion between the elements of the domains. In symbols we write $\mathcal{D}_0 \cong \mathcal{D}_1$. $\square$
It is certain that the property of 1.9 is necessary, but it may not be so clear that it is sufficient. We shall in fact prove in the next lecture that an isomorphism between domains always maps finite elements to finite elements, so it always results from a one-one inclusion-preserving correspondence between neighbourhoods. This is surely as strong as could be hoped. This general result is not needed to see that particular domains are isomorphic.

In some of the examples tokens corresponded to total elements and in some to partial elements; it is not difficult to see (ex post facto) that every domain can be presented with tokens exactly corresponding to partial elements.

**THEOREM 1.10.** Given any neighbourhood system $\mathcal{D}$, define for $X \in \mathcal{D}$

$$
[X] = \{x \in |\mathcal{D}| \mid X \in x\}.
$$

The subsets $[X] \subseteq |\mathcal{D}|$ for $X \in \mathcal{D}$ form a neighbourhood system over $|\mathcal{D}|$ which determines a domain isomorphic to $|\mathcal{D}|$.

**Proof:** We note first that

(1) $[\Delta] = |\mathcal{D}|.$

Next note that

(2) $X, Y$ are consistent in $\mathcal{D}$ iff $[X] \cap [Y] \neq \emptyset$;

and that for $X, Y \in \mathcal{D}$

(3) $[X] \cap [Y] = [X \cap Y]$ if $X \cap Y \in \mathcal{D}.$

Inasmuch as

(4) $\uparrow X \in [X]$ for all $X \in \mathcal{D},$

it easily follows that $\mathcal{D}$ and the family

$$
\{[X] \mid X \in \mathcal{D}\}
$$

are in a one-one, inclusion-preserving correspondence. Thus, we can induce the desired one-one correspondence between the elements of the two systems. $\square$
The import of 1.10 is that the original tokens in $\Delta$ can be replaced by the elements of $|\mathcal{D}|$. This process replaces the neighbourhood $X \subseteq \Delta$ by the subset $[X] \subseteq |\mathcal{D}|$. As the passage is inclusion preserving, the domain has not really changed, only its presentation. Though of some theoretical charm, the theorem is not of much use since we still have to get $\mathcal{D}$ from somewhere. It does emphasize, though, that the rôle of the tokens is simply to keep the inclusions (and intersections) of neighbourhoods sorted out. It is *not* always true that the tokens can be identified with the total elements.

The last theorem in this lecture is a result on *closure properties* of a domain with respect to set-theoretical operations which have interesting meanings with respect to approximation.

**THEOREM 1.11.** If $\mathcal{D}$ is a neighbourhood system and $x_n \in |\mathcal{D}|$ for $n = 0, 1, 2, \ldots$, then

(i) $\bigcap_{n=0}^{\infty} x_n \in |\mathcal{D}|$; and

(ii) $\bigcup_{n=0}^{\infty} x_n \in |\mathcal{D}|$, provided

$$
x_0 \subseteq x_1 \subseteq x_2 \subseteq \cdots \subseteq x_n \subseteq x_{n+1} \subseteq \cdots .
$$

*Proof:* The conditions of 1.6 have to be checked. For the case of intersection, all of 1.6(i)–(iii) are quite obvious. For the case of union, only 1.6(ii) gives pause and it requires the proviso. If $X$ and $Y$ belong to the union, then $X \in x_n$, say, and $Y \in x_m$. But, either $n < m$ or $m < n$, and if $k = \max(n, m)$, then $X, Y \in x_k$. Since $x_k \in |\mathcal{D}|$, we have $X \cap Y \in x_k$; thus, $X \cap Y$ belongs to the union. This proves (ii). $\square$

In words, the intersection is the best element that is at the same time an approximation to all of the elements $x_n$; the intersection is exactly what is common to all the given elements. The union on the other hand is just what the (increas-
The union on the other hand is just what the (increasing sequence of the) $x_n$ approximates; the union combines contributions from all the $x_n$ into a "better" element -- but no more than that.

In thinking about domains a rough diagram of the partial-ordering relation $\subseteq$ between elements is often helpful. The picture of 1.4 is an example where the nodes represent the elements. Any finite tree growing up from a root node would also be an example. Indeed, any finite partially ordered set with least element would be an example. (Here no distinction between tokens and elements is necessary.) A lattice diagram is also illustrated.

**A TREE**

```
        ○
       ╱ ╲
      ○   ○
     ╱│╲ ╱│
    ○ ○ ○ ○
     ╲│╱ ╲│
      ○   ○
       ╲ ╱
        ○
        ⊥
```

**A ROUGH PICTURE**

```
   ∿∿∿∿∿∿∿∿∿∿∿
  ╱ │ │ │ │ ╲
 ╱  │ │ │ │  ╲
╱   │ │ │ │   ╲
╲   │ │ │ │   ╱
 ╲  │ │ │ │  ╱
  ╲ │ │ │ │ ╱
   ╲│ │ │ │╱
    ○
    ⊥
```

**A LATTICE**

```
       ○
      ╱│╲
     ╱ │ ╲
    ○  ○  ○
    │╲ │ ╱│
    │ ╲│╱ │
    ○  ○  ○
     ╲ │ ╱
      ╲│╱
       ○
       ⊥
```

The root node is the element $\perp$ of $|\mathcal{D}|$; there need be no top node $\top$. *Approximation* is represented by a passage from a lower node to a higher node along the rising lines. The system $\mathcal{D}$ of neighbourhoods is the collection of sets each of which is all
the nodes above a given node. For infinite examples, however, care must be given to introduce limit nodes. The first few exercises should be provided with pictures to illustrate the structure.

## EXERCISES

**EXERCISE 1.12.** Let $\Delta = \mathbb{N} = \{0, 1, 2, \ldots, n, \ldots\}$ be the set of non-negative integers. Use as neighbourhoods final segments:

$$
\{m \in \mathbb{N} \mid m > n\}
$$

for $n \in \mathbb{N}$. Verify that this is a neighbourhood system. What are the total elements? What are the finite elements? Draw a picture of the approximation relation in this domain. (Hint: there is only one limit element.)

**EXERCISE 1.13.** Verify all the assertions made about the system $B$ defined as the infinite generalization of Example 1.4. Draw a picture similar to that given in the text which includes nodes for all $\sigma \in \Sigma^*$. Show the neighbourhoods, how the approximation relation behaves, and where the total elements lie. (The picture is closely related to the "binary tree", but has to have limit nodes all along the top.)

**EXERCISE 1.14.** Let $\Delta = \mathbb{N}$ and let $\mathcal{V}$ be the family of finite non-empty subsets of $\Delta$ plus the set $\Delta$. Show that this is a neighbourhood system. What are the total elements? What are the finite elements? Draw a picture.

**EXERCISE 1.15.** Construct non-isomorphic infinite domains where all elements are finite but where there are no infinite chains $\langle x_n \rangle_{n=0}^{\infty}$ of elements with $x_n \sqsubseteq x_{n+1}$ but $x_n \neq x_{n+1}$ for all $n$.
**EXERCISE 1.16.** Let $\Delta = \mathbf{N}$ and let $\mathcal{D}$ be the family of *cofinite* subsets of $\mathbf{N}$. Show that $|\mathcal{D}|$ is isomorphic to the partially ordered set of *all* subsets of $\mathbf{N}$ under inclusion. Construct some other neighbourhood systems where $\mathcal{D}$ is closed under finite intersection. What happens to the total elements in such systems?

**EXERCISE 1.17.** Let $\Delta = \mathbf{R}$ be the real line. Let $\mathcal{D}$ be the set of non-empty open intervals with rational end points plus the set $\Delta$. Show that this is a neighbourhood system. For any real $t \in \mathbf{R}$, show that $\{ X \in \mathcal{D} \mid t \in X \}$ is a filter. Is it always total? What are the total elements of $|\mathcal{D}|$? (Hint: When $t$ is rational consider all intervals with $t$ as a right-hand end point.)

**EXERCISE 1.18.** Let $\mathcal{D}$ be a neighbourhood system. Call a subset $C \subseteq \mathcal{D}$ *consistent* iff every finite subset of $C$ is consistent in $\mathcal{D}$. Give an example where $C$ is a subset with more than two elements, every pair of neighbourhoods in $C$ is consistent, but $C$ is *not* consistent. Show that if $C$ is consistent, then there is a *least* filter $x \in |\mathcal{D}|$ with $C \subseteq x$. Show generally that the *intersection* of any non-empty collection of filters is again a filter.

**EXERCISE 1.19.** Define a *positive neighbourhood system* to be a family $\mathcal{D}$ where (ii) of 1.1 is replaced by **(ii')** whenever $X, Y \in \mathcal{D}$, then $X \cap Y \neq \emptyset$ iff $X \cap Y \in \mathcal{D}$. Prove that a positive neighbourhood system is indeed a neighbourhood system in the sense of the earlier definition. Give an example of a neighbourhood system that is *not* positive. (Hint: (suggested by C.A.R. Hoare). Let $\Delta = \mathbf{N} \times \mathbf{N}$, in the plane. Let $\mathcal{D}$ be the family of subsets $X \subseteq \mathbf{N} \times \mathbf{N}$ where all but a finite number of places the *vertical* sections of $X$ are the whole of $\mathbf{N}$ but at the other places the sections are finite and nonempty. Smaller examples are of course possible.)
**EXERCISE 1.20.** Let $\mathcal{D}$ be any neighbourhood system over a set $\Delta$. Let $\Delta' = \mathcal{D}$ and define

$$
\mathcal{D}' = \{ \uparrow X \mid X \in \mathcal{D} \},
$$

where

$$
\uparrow X = \{ Y \in \mathcal{D} \mid Y \subseteq X \}.
$$

Show that $\mathcal{D}'$ is a positive neighbourhood system and that $|\mathcal{D}|$ and $|\mathcal{D}'|$ are isomorphic. Note that for $\mathcal{D}'$ finite elements and tokens are in a one-one correspondence.

**EXERCISE 1.21.** Work out in greater detail the proof of 1.10. Remark that the neighbourhood system over $|\mathcal{D}|$ so constructed is positive, thereby obtaining in a different way the same kind of conclusion as in 1.20. Show also that the system over $|\mathcal{D}|$ is complete in the sense that every filter is fixed by a unique member of the underlying set. (A filter is *fixed by a point* iff it is the filter of *all* neighbourhoods containing that point.) Remark that a complete system is one where tokens and (partial) elements can always be identified (under a suitable one-one correspondence). Show also that consistency of a set $\{ X_i \mid i < n \}$ of neighbourhoods in $\mathcal{D}$ is equivalent to saying

$$
\bigcap_{i < n} [ X_i ] \neq \emptyset.
$$

**EXERCISE 1.22.** (For topologists). Show that the neighbourhoods $[X]$ for $X \in \mathcal{D}$ make $|\mathcal{D}|$ into a topological space where the open subsets $\mathcal{U} \subseteq |\mathcal{D}|$ can be characterized by the following two conditions:

(i) whenever $x \in \mathcal{U}$ and $x \sqsubseteq y \in |\mathcal{D}|$, then $y \in \mathcal{U}$; and

(ii) whenever $x \in \mathcal{U}$, then $[X] \in \mathcal{U}$ for some $X \in x$.

Prove also that the inclusion relation on $|\mathcal{D}|$ can be defined topologically as:

(iii) $x \sqsubseteq y$ iff for all open $\mathcal{U} \subseteq |\mathcal{D}|$, if $x \in \mathcal{U}$ then $y \in \mathcal{U}$.
Is $|D|$ ever a Hausdorff space?

Show that if $(x_n)_{n=0}^{\infty}$ is a sequence of elements of $|D|$ with $x_n \subseteq x_{n+1}$ for all $n$, then

$$
\bigcup_{n=0}^{\infty} x_n
$$

is not only in $|D|$ but is a topological limit point of the sequence. Show that any element $x$ is a limit point of the set $\{\uparrow X \mid X \in x\}$. Are there other limit points?

**EXERCISE 1.23.** Suppose that the neighbourhood system $D$ is countable, say,

$$
D = \{X_0, X_1, X_2, \ldots, X_n, \ldots\}.
$$

Suppose further that the property of consistency of finite sequences of neighbourhoods is decidable (or "effectively known"). Then the following sequence is well defined:

$$
\begin{aligned}
Y_0 &= X_0 \\
Y_{n+1} &= X_{n+1}, \text{ if this set is consistent with } Y_0, Y_1, \ldots, Y_n; \\
&= Y_n, \text{ if not.}
\end{aligned}
$$

Show that $\{Y_0, Y_1, \ldots, Y_n, \ldots\}$ is a total element of $|D|$. (Hint: Show first that $Y_0, Y_1, \ldots, Y_{n-1}$ is consistent for all $n$.) In such a system show that all filters can be determined by sequences.

**EXERCISE 1.24.** (For set theorists). Prove, using the Axiom of Choice, or some equivalent principle, that in every domain a partial element can always be extended to a total element. Is this assertion equivalent to the Axiom of Choice? (Hint: Remember to prove that the union of every (transfinite) chain of filters is again a filter.)
**EXERCISE 1.25.** (For set theorists). Let $\Delta$ be any well-ordered set (ordinal). (Even small ordinals like $\omega \cdot 3$ or $\omega^5$ are interesting.) Let $\mathcal{D}$ be the family of non-empty *final* segments of $\Delta$. What is $|\mathcal{D}|$? Are all elements finite? Is every approximation to a finite element finite?

**EXERCISE 1.26.** (For algebraists). Let $A$ be a commutative ring with unit. Let $\Delta$ be the set of finite subsets $F \subseteq A$. Define

$$
I(F) = \{G \in \Delta \mid F \subseteq \text{the ideal generated by } G\}.
$$

Prove that the sets of the form $I(F)$ form a neighbourhood system, and that the corresponding domain is isomorphic to the set of ring-theoretic ideals of $A$ partially ordered by inclusion. What would happen if we excluded from $\Delta$ all $F$ with $I(F) = I(\{1\})$, where $1$ is the unit of $A$?

**EXERCISE 1.27.** Further closure properties of domains can be proved for bounded sets. We say $X \subseteq |\mathcal{D}|$ is *bounded* iff for some $y \in |\mathcal{D}|$ we have $x \subseteq y$ for all $x \in X$. This $y$ is called an *upper bound*. We let

$$
\bigsqcup X = \bigcap \{y \in |\mathcal{D}| \mid x \subseteq y \text{ all } x \in X\}.
$$

Prove that if $X$ is bounded, then $\bigsqcup X$ is the *least upper bound* for $X$ in $|\mathcal{D}|$. Prove also: if $U, V \in \mathcal{D}$ are neighbourhoods, then $\{U, V\}$ is consistent in $\mathcal{D}$ iff $\{\uparrow U, \uparrow V\}$ is bounded in $|\mathcal{D}|$. (That is, boundedness is for elements what consistency is for neighbourhoods.) Prove finally with the aid of 1.18 that $X \subseteq |\mathcal{D}|$ is bounded iff every finite subset of $X$ is bounded.

**Lean 4**

- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Basic/notation40.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Basic/notation40.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/BasicInst22.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/BasicInst22.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/BasicInst34.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/BasicInst34.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Consistent.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Consistent.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/DomainIso.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/DomainIso.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Element.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Element.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/Token.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/Token.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_is_unique_partial.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_is_unique_partial.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_lt_elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_lt_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_lt_elemZero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_lt_elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/elemZero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/element_classification.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/element_classification.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/eq_bot_of_le_elemZero_of_le_elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/eq_bot_of_le_elemZero_of_le_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/eq_of_master_subset.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/eq_of_master_subset.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/inter_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/inter_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/inter_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/inter_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_not_subset_one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_not_subset_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_not_subset_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_not_subset_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/memSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/memSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/neighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_elemOne_le_elemZero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_elemOne_le_elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_elemZero_le_elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_elemZero_le_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_mem_empty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_mem_empty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one_inter_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one_inter_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one_not_subset_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one_not_subset_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero_inter_one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero_inter_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero_not_subset_one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero_not_subset_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/Token.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/Token.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/bot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/bot_lt_elemTwelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/bot_lt_elemTwelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwelve_lt_elemTwo.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwelve_lt_elemTwo.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwo.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwo.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwo_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwo_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/element_classification.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/element_classification.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/eq_of_master_subset.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/eq_of_master_subset.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/inter_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/inter_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/inter_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/inter_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_not_subset_twelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_not_subset_twelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_not_subset_two.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_not_subset_two.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/memSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/memSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_twelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_twelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_two.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_two.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/neighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve_inter_two.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve_inter_two.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve_not_subset_two.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve_not_subset_two.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/two.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/two.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/two_inter_twelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/two_inter_twelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/Token.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/Token.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot_lt_elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot_lt_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot_lt_elemZero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot_lt_elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem00_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem00_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem01_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem01_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem10_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem10_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem11_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem11_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne_lt_elem10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne_lt_elem10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne_lt_elem11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne_lt_elem11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero_lt_elem00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero_lt_elem00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero_lt_elem01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero_lt_elem01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/element_classification.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/element_classification.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/eq_of_master_subset.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/eq_of_master_subset.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/inter_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/inter_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/inter_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/inter_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/master_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/master_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/memSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/memSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/neighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/not_mem_empty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/not_mem_empty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/P4Mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/P4Mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/P4_inter_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/P4_inter_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/P4_master_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/P4_master_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/P4_master_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/P4_master_nonempty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/P4_sub_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/P4_sub_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/Token.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/Token.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/consistent_iff_inter_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/consistent_iff_inter_nonempty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/mem_iff_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/mem_iff_nonempty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/neighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example15/neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/B.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/B.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/B_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/B_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/B_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/B_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/Str.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/Str.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/bot_mem_cone_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/bot_mem_cone_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/cone.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/cone.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/cone_injective.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/cone_injective.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/cone_nil.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/cone_nil.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/cone_subset_cone.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/cone_subset_cone.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/cone_trichotomy.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/cone_trichotomy.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/memB.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/memB.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/memB_cone.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/memB_cone.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/memB_prepend.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/memB_prepend.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/mem_cone.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/mem_cone.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/mem_iff_exists_sigmaBot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/mem_iff_exists_sigmaBot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/mem_prepend.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/mem_prepend.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/nestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/nestedOrDisjoint.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend_append.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend_append.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend_cone.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend_cone.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend_mono.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend_mono.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend_nil.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend_nil.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend_univ.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/prepend_univ.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaBot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaBot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaBot_le_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaBot_le_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaElt.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaElt.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaElt_append.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaElt_append.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaElt_bot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaElt_bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaElt_nil.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ExampleB/sigmaElt_nil.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/element_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/element_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin_le_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin_le_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin_strictMono.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin_strictMono.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/isTotal_iff_top.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/isTotal_iff_top.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/le_top.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/le_top.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem_tail.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem_tail.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem_tail_nbhd.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem_tail_nbhd.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/neighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/nestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/nestedOrDisjoint.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/ns_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/ns_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail_subset_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail_subset_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/top.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/top.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/top_isTotal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/top_isTotal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branch.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branch.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branchSeq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branchSeq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branchSeq_le_branch.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branchSeq_le_branch.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branchSeq_mono.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branchSeq_mono.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branch_isTotal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branch_isTotal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branch_mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/branch_mem_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/prefixSeq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/prefixSeq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/prefixSeq_length.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/prefixSeq_length.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/prefixSeq_mono.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/prefixSeq_mono.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/prefixSeq_prefix_succ.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/prefixSeq_prefix_succ.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/prefix_comparable_of_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise113/prefix_comparable_of_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/bot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/empty_not_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/empty_not_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/fin.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/fin.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/mem_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/mem_singleton.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/neighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/nonempty_of_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/nonempty_of_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/ns_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/ns_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/singleton_isTotal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise114/singleton_isTotal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flatMem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flatMem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flatNOD.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flatNOD.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_all_finite.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_all_finite.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_atom_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_atom_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_classify.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_classify.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_empty_not_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_empty_not_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_infinite.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_infinite.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_mem_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_mem_singleton.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_no_infinite_chain.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_no_infinite_chain.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_no_three_chain.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/flat_no_three_chain.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/not_isomorphic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/not_isomorphic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/singleton_disjoint.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/singleton_disjoint.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stemMem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stemMem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stemNOD.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stemNOD.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem_mem_pair.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem_mem_pair.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem_mem_univ.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem_mem_univ.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem_mem_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem_mem_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem_principal_lt.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem_principal_lt.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem_three_chain.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise115/stem_three_chain.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/cofiniteIso.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/cofiniteIso.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/cofiniteSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/cofiniteSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/cofiniteSystem_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/cofiniteSystem_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/fullSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/fullSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/le_ofExcluded_univ.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/le_ofExcluded_univ.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/mem_compl_of_finite.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/mem_compl_of_finite.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/mem_compl_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/mem_compl_singleton.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/mem_ofExcluded.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/mem_ofExcluded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/mem_toExcluded.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/mem_toExcluded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/ofExcluded.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/ofExcluded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/ofExcluded_toExcluded.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/ofExcluded_toExcluded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/ofExcluded_univ_isTotal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/ofExcluded_univ_isTotal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/subset_compl_singleton.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/subset_compl_singleton.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/toExcluded.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/toExcluded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/toExcluded_ofExcluded.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise116/toExcluded_ofExcluded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/filterAt.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/filterAt.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/filterAt_injective.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/filterAt_injective.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/inter_mem'.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/inter_mem'.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/ratIntervalMem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/ratIntervalMem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/ratIntervalMem_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/ratIntervalMem_nonempty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/ratIntervalSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/ratIntervalSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/ratIntervalSystem_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise117/ratIntervalSystem_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/A.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/A.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/B.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/B.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/Cc.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/Cc.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/FinitelyConsistent.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/FinitelyConsistent.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/appendSeq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/appendSeq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/appendSeq_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/appendSeq_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/family.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/family.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/family_pairwise_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/family_pairwise_nonempty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/interUpTo_appendSeq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/interUpTo_appendSeq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/interUpTo_appendSeq_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/interUpTo_appendSeq_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/interUpTo_subset_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/interUpTo_subset_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/le_sInf.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/le_sInf.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/leastFilter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/leastFilter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/leastFilter_le.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/leastFilter_le.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/not_finitelyConsistent.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/not_finitelyConsistent.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/sInf.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/sInf.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/sInf_le.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/sInf_le.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/subset_leastFilter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/subset_leastFilter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/triSys.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/triSys.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/triSys_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/triSys_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/triple.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/triple.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/triple_interUpTo_empty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/triple_interUpTo_empty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/triple_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise118/triple_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/Tok.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/Tok.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/a.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/a.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/a_inter_b.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/a_inter_b.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/b.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/b.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/inter_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/inter_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/memSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/memSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/mem_a.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/mem_a.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/mem_b.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/mem_b.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/mem_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/mem_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/notPositiveSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/notPositiveSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/not_isPositive.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/not_isPositive.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/not_mem_sub_one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/not_mem_sub_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/one_not_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/one_not_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/positiveExample.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/positiveExample.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/positiveExample_isPositive.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise119/positiveExample_isPositive.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/isomorphic_powerSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/isomorphic_powerSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/mem_upSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/mem_upSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/ofPower.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/ofPower.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/powerIso.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/powerIso.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/powerSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/powerSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/powerSystem_isPositive.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/powerSystem_isPositive.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/powerSystem_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/powerSystem_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/toPower.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/toPower.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/toPower_principal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/toPower_principal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/upSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/upSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/upSet_injective.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/upSet_injective.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/upSet_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/upSet_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/upSet_subset_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise120/upSet_subset_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/IsComplete.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/IsComplete.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/bracket_nonempty_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/bracket_nonempty_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/consistent_iff_bracket_interUpTo_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/consistent_iff_bracket_interUpTo_nonempty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/consistent_iff_iInter_bracket_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/consistent_iff_iInter_bracket_nonempty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/filterFixedBy.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/filterFixedBy.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/tokenSystem_complete.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/tokenSystem_complete.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/tokenSystem_isPositive.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/tokenSystem_isPositive.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/tokenSystem_toToken_bijective.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise121/tokenSystem_toToken_bijective.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/IsOpenFilter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/IsOpenFilter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/basicOpen.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/basicOpen.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_basicOpen.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_basicOpen.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_iff_isOpenFilter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_iff_isOpenFilter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_iff_upper_basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_iff_upper_basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_isUpperSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/isOpen_isUpperSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/le_iff_isOpen_imp.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/le_iff_isOpen_imp.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/mem_basicOpen.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/mem_basicOpen.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/specializes_iff_le.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise122/specializes_iff_le.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise123.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise123.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise124.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise124.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise124/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise124/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise124/chainUnion.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise124/chainUnion.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise124/exists_total_ge.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise124/exists_total_ge.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise124/le_chainUnion.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise124/le_chainUnion.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/Ici_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/Ici_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/exists_Ici_of_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/exists_Ici_of_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/finalSegmentClassify.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/finalSegmentClassify.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/finalSegmentSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/finalSegmentSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/lowerSetOf.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/lowerSetOf.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/lowerSetOf_isLowerSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/lowerSetOf_isLowerSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/lowerSetOf_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/lowerSetOf_nonempty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/lowerSetOf_ofLowerSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/lowerSetOf_ofLowerSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/master_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/master_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/mem_def.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/mem_def.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/ofLowerSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/ofLowerSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/ofLowerSet_lowerSetOf.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/ofLowerSet_lowerSetOf.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/principal_Ici_le_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/principal_Ici_le_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/topElement.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/topElement.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/upperSet_subset_or.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise125/upperSet_subset_or.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/IFamily.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/IFamily.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/IFamily_eq_of_span_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/IFamily_eq_of_span_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/IFamily_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/IFamily_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/IFamily_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/IFamily_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/IFamily_subset_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/IFamily_subset_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/idealOf.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/idealOf.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/idealOf_ofIdeal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/idealOf_ofIdeal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/mem_IFamily.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/mem_IFamily.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/mem_IFamily_of_forall.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/mem_IFamily_of_forall.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/mem_idealOf.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/mem_idealOf.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/mem_ofIdeal_IFamily.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/mem_ofIdeal_IFamily.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/ofIdeal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/ofIdeal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/ofIdeal_idealOf.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/ofIdeal_idealOf.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/ringIso.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/ringIso.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/ringSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/ringSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/ringSystem_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/ringSystem_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/span_eq_of_IFamily_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise126/span_eq_of_IFamily_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/Bounded.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/Bounded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/bounded_iff_finite_bounded.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/bounded_iff_finite_bounded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/consistent_pair_iff_bounded.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/consistent_pair_iff_bounded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/interUpTo_pairSeq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/interUpTo_pairSeq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/le_sSup.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/le_sSup.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/pairSeq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/pairSeq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/sSup.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/sSup.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/sSup_le.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/sSup_le.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/upperBounds.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/upperBounds.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/upperBounds_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/upperBounds_nonempty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/IsPositive.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/IsPositive.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/IsTotal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/IsTotal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Isomorphic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Isomorphic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/NeighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/NeighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/NestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/NestedOrDisjoint.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/SeqEquiv.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/SeqEquiv.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket_injective.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket_injective.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket_inter_nonempty_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket_inter_nonempty_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket_subset_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/bracket_subset_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/isomorphic_tokenSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/isomorphic_tokenSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/mem_bracket.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/mem_bracket.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/ofToken.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/ofToken.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/principal_mem_bracket.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/principal_mem_bracket.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/toToken.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/toToken.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/tokenIso.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/tokenIso.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/tokenSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/tokenSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/tokenSystem_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem110/tokenSystem_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/iInter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/iInter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/iInter_le.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/iInter_le.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/iUnion.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/iUnion.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/iUnion_le.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/iUnion_le.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/le_iInter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/le_iInter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/le_iUnion.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/le_iUnion.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/mem_iInter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Theorem111/mem_iInter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Y.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Y.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Y_succ_neg.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Y_succ_neg.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Y_succ_pos.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Y_succ_pos.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Y_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Y_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc_eq_interUpTo.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc_eq_interUpTo.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc_succ_neg.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc_succ_neg.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc_succ_pos.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc_succ_pos.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/acc_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/bot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/bot_le.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/bot_le.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/cond.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/cond.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/element_le.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/element_le.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/element_le_antisymm.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/element_le_antisymm.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/element_le_refl.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/element_le_refl.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/element_le_trans.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/element_le_trans.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ext.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ext.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/greedyElement.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/greedyElement.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/interUpTo.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/interUpTo.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/interUpTo_antitone.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/interUpTo_antitone.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/interUpTo_succ.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/interUpTo_succ.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/interUpTo_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/interUpTo_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/limitFamily.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/limitFamily.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/mem_bot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/mem_bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/mem_interUpTo_Y.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/mem_interUpTo_Y.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/mem_principal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/mem_principal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ofNestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ofNestedOrDisjoint.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ofPositive.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/ofPositive.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/principal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/principal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/state.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/state.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/state_succ.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/state_succ.lean)
