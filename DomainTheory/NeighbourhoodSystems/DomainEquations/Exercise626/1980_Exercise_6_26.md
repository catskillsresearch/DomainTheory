# Exercise 6.26

**EXERCISE 6.26.** For systems $\mathcal{D}$ as in 6.19 define

$$\mathcal{D}_\perp = \{ \{\Lambda\} \cup 0\Delta \} \cup \{ 0X \mid X \in \mathcal{D} \}.$$

Describe the construct in terms of elements. Is this a suitable functor? Prove that

$$\mathcal{D}_\perp \oplus \mathcal{E}_\perp \cong \mathcal{D} + \mathcal{E}.$$

What is

$$\mathcal{D}_\perp \otimes \mathcal{E}_\perp \cong \ ??$$

**Lean 4**

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
