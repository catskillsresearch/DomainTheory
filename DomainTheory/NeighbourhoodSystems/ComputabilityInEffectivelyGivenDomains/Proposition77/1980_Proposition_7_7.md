# Proposition 7.7

The major consequence of what we have done up to this point concerns typed $\lambda$-calculus. Any expression involving only *effectively given types* and, perhaps, some *basic computable constants* using only the $\lambda, !$-notation defines a computable function of its free variables. And such functions applied to computable arguments give computable values. And such functions have computable least fixed points. Etc., etc. In a definite sense then we have in the “metalanguage”, as people say, a quite precise and fully *mathematical programming language* for defining computable operators. It is not a machine implemented language, but it is a mathematically well-defined and easy-to-use language. And when we combine the usual type-definition facility together with *domain equations*, we have an especially powerful language.

**PROPOSITION 7.7.** For any effectively given domain $D$, the domain $D^\S$ is also effectively given, and all the combinators of Example 6.1 prove to be computable.

*Proof:* This proof is essentially an exercise, but it is useful to have an easy-to-grasp example. Indeed, to make things easy to reason about, we can assume that $D$ is a system over $\Delta = \mathbf{N}$, and that in the presentation where

$$D = \{ X_n \mid n \in \mathbf{N} \},$$

the relation $k \in X_n$ is *recursive* in $k$ and $n$. (It is worth thinking why this is so.) Of course, a lot of other things are recursive also.
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
$$V_m \ \mathrm{proj}_0 \ V_k \text{ iff } k = 0 \text{ or } \exists n \in \mathbf{N}.\, m = 2n + 2 \text{ and } V_{p(n)} \subseteq V_k.$$

The reader should write out other cases. $\square$

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77.lean](../Proposition77.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp.lean](Vsharp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_eq_Gamma_iff.lean](Vsharp_eq_Gamma_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_even.lean](Vsharp_even.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_even_inter_even.lean](Vsharp_even_inter_even.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_even_inter_odd.lean](Vsharp_even_inter_odd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_inter_zero.lean](Vsharp_inter_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_mem.lean](Vsharp_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_nonempty.lean](Vsharp_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_odd.lean](Vsharp_odd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_odd_inter_even.lean](Vsharp_odd_inter_even.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_odd_inter_odd.lean](Vsharp_odd_inter_odd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_succ.lean](Vsharp_succ.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_surj.lean](Vsharp_surj.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_zero.lean](Vsharp_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/Vsharp_zero_inter.lean](Vsharp_zero_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/consB.lean](consB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/consB_packT.lean](consB_packT.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpPresentation.lean](dsharpPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep.lean](dsharpStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_i0.lean](dsharpStep_i0.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_j0.lean](dsharpStep_j0.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_ll.lean](dsharpStep_ll.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_ln.lean](dsharpStep_ln.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_nl.lean](dsharpStep_nl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharpStep_nn.lean](dsharpStep_nn.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_decider_spec.lean](dsharp_decider_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_intI_correct.lean](dsharp_intI_correct.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_interEq_iff.lean](dsharp_interEq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/dsharp_isEffectivelyGiven.lean](dsharp_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/eqB.lean](eqB.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/eqB_packT.lean](eqB_packT.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/exists_sub_embPair_iff.lean](exists_sub_embPair_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/exists_sub_embZero_iff.lean](exists_sub_embZero_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gList.lean](gList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gList_length.lean](gList_length.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gOf.lean](gOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/gOf_def.lean](gOf_def.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/getD_gList.lean](getD_gList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/intI.lean](intI.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/intI_packT.lean](intI_packT.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/le_pair_left.lean](le_pair_left.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet.lean](listGet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGetStp.lean](listGetStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGetStp_pair.lean](listGetStp_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_encodeList.lean](listGet_encodeList.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_foldl.lean](listGet_foldl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_foldl_zero.lean](listGet_foldl_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/listGet_rtbl.lean](listGet_rtbl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/max_sq_le_pair.lean](max_sq_le_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/memS_sub_embPair.lean](memS_sub_embPair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/memS_sub_embZero.lean](memS_sub_embZero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/nat_shape.lean](nat_shape.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/packT.lean](packT.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/pair_lt_pair_of_lt.lean](pair_lt_pair_of_lt.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/pair_lt_succ_sq.lean](pair_lt_succ_sq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_dsharpStep.lean](primrec_dsharpStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_gOf.lean](primrec_gOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_listGet.lean](primrec_listGet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_listGet₂.lean](primrec_listGet₂.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/primrec_rtbl.lean](primrec_rtbl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/rtbl.lean](rtbl.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/rtbl_eq_encode.lean](rtbl_eq_encode.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/rtbl_eq_rec.lean](rtbl_eq_rec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition77/unpair_fst_le.lean](unpair_fst_le.lean)
