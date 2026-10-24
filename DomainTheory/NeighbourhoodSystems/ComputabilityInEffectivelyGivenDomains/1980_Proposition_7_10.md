# Proposition 7.10

## Human-English

**PROPOSITION 7.10.** The power domain $\mathbb{P}\mathcal{D}$ is a neighbourhood system if $\mathcal{D}$ is, and it is effectively given if $\mathcal{D}$ is.

*Proof* : The system $\mathcal{D}^\dagger$ is a neighbourhood system as we just remarked; indeed it is a positive neighbourhood system. It is easy to prove that the closure of any positive system under finite unions is a neighbourhood system, because the resulting family of sets is closed under *all* finite intersections. (If we left out the empty union, the result would be a positive system.) The proof is obvious since intersection of sets distributes over finite union. So $\mathbb{P}\mathcal{D}$ is a neighbourhood system.

For the second half of the proposition, we just have to constructivize the previous argument. Thus, if

$$\mathcal{D} = \{ X_n \mid n \in \mathbb{N} \},$$

then the elements of $\mathbb{P}\mathcal{D}$ can be written as:

$$\bigcup_{i < q} (\downarrow X_{n_i}),$$

<!-- page 128 -->

and hence are indexed by the finite sequences $\langle n_0, \dots, n_{q-1} \rangle$ of integers. Now one of the standard devices of recursion theory is to put the finite sequences of integers into a recursive one-one correspondence with the integers themselves. This is the start of the recursive presentation of $\mathbb{P}\mathcal{D}$, since it means we can list effectively all the required neighbourhoods.

Next consider an intersection

$$\bigcup_{i < q} (\downarrow X_{n_i}) \cap \bigcup_{j < r} (\downarrow X_{m_j}) = \bigcup_{\substack{i < q \\ j < r}} \downarrow (X_{n_i} \cap X_{m_j}) \, .$$

Some of the terms which are $\emptyset$ have to be thrown out — but this requires only a finite number of decisions all computable by assumption. Now we have to rewrite

$$X_{n_i} \cap X_{m_j} = X_{k_{ij}} \, ,$$

but the finding of $k_{ij}$ is also computable. *Finally*, we have to re-order the doubly indexed sequence into a singly indexed sequence of length $q \cdot r$, but this is easily seen to be computable also. Therefore, intersections can be "calculated".

It remains to be shown that equality between neighbourhoods in $\mathbb{P}\mathcal{D}$ is decidable. The question really comes down to deciding something like:

$$\downarrow X_k \subseteq \bigcup_{i < q} \downarrow X_{n_i} \, .$$

Now since $X_k \in \downarrow X_k$, we find that the above is just equivalent to:

$$\exists i < q \ldotp X_k \subseteq X_{n_i} \, .$$

By our assumptions on $\mathcal{D}$, this is decidable. (It is this part of the argument that required the passage to $\mathcal{D}^\dagger$. It does not seem to be generally true that the closure under finite unions of an effectively given system is again effectively given.) $\square$

One of the main reasons that $\mathbb{P}\mathcal{D}$ is like a power domain is the possibility of forming "finite sets".

<!-- page 129 -->

## AI: Human-English to AI-Lean

**[Proposition_7_10.lean](Proposition_7_10.lean)**

@import "Proposition_7_10.lean"
