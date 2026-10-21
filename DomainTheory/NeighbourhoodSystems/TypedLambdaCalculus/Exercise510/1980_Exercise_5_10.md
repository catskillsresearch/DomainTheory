# Exercise 5.10

**EXERCISE 5.10.** Suppose $\mathcal{D}_0$ and $\mathcal{D}_1$ are neighbourhood systems over disjoint sets $\Delta_0$ and $\Delta_1$. Define the *smash product* $\mathcal{D}_0 \otimes \mathcal{D}_1$ with neighbourhoods

$$
\{\Delta_0 \cup \Delta_1\} \cup \{X \cup Y \mid X \in \mathcal{D}_0 \setminus \{\Delta_0\} \text{ and } Y \in \mathcal{D}_1 \setminus \{\Delta_1\}\}.
$$

Show that this *is* a neighbourhood system. Define $(\mathcal{D}_0 \to_\bot \mathcal{D}_1)$ so that $|\mathcal{D}_0 \to_\bot \mathcal{D}_1|$ consists exactly of the *strict functions*. By introducing appropriate combinators, show that

$$
(\mathcal{D}_0 \to_\bot (\mathcal{D}_1 \to_\bot \mathcal{D}_2)) \quad \text{and} \quad ((\mathcal{D}_0 \otimes \mathcal{D}_1) \to_\bot \mathcal{D}_2)
$$

are isomorphic.

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510.lean](../Exercise510.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/IsStrict.lean](IsStrict.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/SmashProper.lean](SmashProper.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/StrictMap.lean](StrictMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/eq_bot_of_no_proper.lean](eq_bot_of_no_proper.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/exists_proper_of_ne_bot.lean](exists_proper_of_ne_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/inter_ne_master_left.lean](inter_ne_master_left.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/inter_ne_master_right.lean](inter_ne_master_right.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_constBot.lean](isStrict_constBot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_idMap.lean](isStrict_idMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_iff_apply_bot.lean](isStrict_iff_apply_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/isStrict_smashSection.lean](isStrict_smashSection.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_smashPair.lean](mem_smashPair.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_sstep.lean](mem_sstep.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_sstepFun.lean](mem_sstepFun.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_sstepFun_iff.lean](mem_sstepFun_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mem_toStrictFilter.lean](mem_toStrictFilter.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/mono.lean](mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/principal_master_eq_bot.lean](principal_master_eq_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/rel_sstepFun_iff.lean](rel_sstepFun_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/section_uncurry_rel.lean](section_uncurry_rel.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash.lean](smash.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashCurryEquiv.lean](smashCurryEquiv.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashCurryMap.lean](smashCurryMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashCurry_uncurry.lean](smashCurry_uncurry.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair.lean](smashPair.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_bot_left.lean](smashPair_bot_left.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_bot_right.lean](smashPair_bot_right.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_eq_bot_iff.lean](smashPair_eq_bot_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_mono.lean](smashPair_mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashPair_principal_apply.lean](smashPair_principal_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashSection.lean](smashSection.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashSection_mono.lean](smashSection_mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashSection_rel.lean](smashSection_rel.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashUncurryMap.lean](smashUncurryMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smashUncurry_curry.lean](smashUncurry_curry.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_master.lean](smash_master.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_bot.lean](smash_mem_bot.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_iff.lean](smash_mem_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_prodNbhd_form.lean](smash_mem_prodNbhd_form.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/smash_mem_proper.lean](smash_mem_proper.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep.lean](sstep.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun.lean](sstepFun.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_append.lean](sstepFun_append.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_cons.lean](sstepFun_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_nil.lean](sstepFun_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_singleton.lean](sstepFun_singleton.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstepFun_up_closed.lean](sstepFun_up_closed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_cod_master.lean](sstep_cod_master.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_inter_right.lean](sstep_inter_right.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_master_eq.lean](sstep_master_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_mem_of_mem.lean](sstep_mem_of_mem.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/sstep_subset.lean](sstep_subset.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun.lean](strictFun.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFunEquiv.lean](strictFunEquiv.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_master.lean](strictFun_master.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_mem_iff.lean](strictFun_mem_iff.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_mem_inter.lean](strictFun_mem_inter.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/strictFun_mem_up_closed.lean](strictFun_mem_up_closed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/toStrictFilter.lean](toStrictFilter.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/toStrictMap.lean](toStrictMap.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise510/toStrictMap_rel.lean](toStrictMap_rel.lean)
