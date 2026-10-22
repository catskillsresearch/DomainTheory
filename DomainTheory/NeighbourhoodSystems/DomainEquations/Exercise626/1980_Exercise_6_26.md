# Exercise 6.26

**EXERCISE 6.26.** For systems $\mathcal{D}$ as in 6.19 define

$$\mathcal{D}_\perp = \{ \{\Lambda\} \cup 0\Delta \} \cup \{ 0X \mid X \in \mathcal{D} \}.$$

Describe the construct in terms of elements. Is this a suitable functor? Prove that

$$\mathcal{D}_\perp \oplus \mathcal{E}_\perp \cong \mathcal{D} + \mathcal{E}.$$

What is

$$\mathcal{D}_\perp \otimes \mathcal{E}_\perp \cong \ ??$$

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/Exercise626/liftBot_le.lean](liftBot_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftBot_lt_liftUp.lean](liftBot_lt_liftUp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok_comp.lean](liftMapTok_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok_id.lean](liftMapTok_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok_isStrict.lean](liftMapTok_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTokMaster.lean](liftTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/embF_subset_liftTokMaster.lean](embF_subset_liftTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTokMaster_inter_embF.lean](liftTokMaster_inter_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_mem_master.lean](liftTok_mem_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftUp_le_liftUp_iff.lean](liftUp_le_liftUp_iff.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftUp_unlift.lean](liftUp_unlift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/eq_liftBot_or_exists_liftUp.lean](eq_liftBot_or_exists_liftUp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/lift_oplus_lift_iso_sum.lean](lift_oplus_lift_iso_sum.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/lift_otimes_lift_iso_lift_prod.lean](lift_otimes_lift_iso_lift_prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626.lean](../Exercise626.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/nil_mem_liftTokMaster.lean](nil_mem_liftTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/embF_ne_liftTokMaster.lean](embF_ne_liftTokMaster.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTok.lean](liftTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftBot.lean](liftBot.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_mem_embF.lean](liftTok_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_mem_embF_inv.lean](liftTok_mem_embF_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftTok_nonempty.lean](liftTok_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/lift.lean](lift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftUp.lean](liftUp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/mem_liftBot.lean](mem_liftBot.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/mem_liftUp.lean](mem_liftUp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftMapTok.lean](liftMapTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/o_embFF_inv.lean](o_embFF_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/o_embTF_inv.lean](o_embTF_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/o_mem_embFF.lean](o_mem_embFF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/o_mem_embTF.lean](o_mem_embTF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift.lean](toSumLift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift_mem_embF.lean](toSumLift_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift_mem_embT.lean](toSumLift_mem_embT.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift.lean](fromSumLift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift_mem_embFF.lean](fromSumLift_mem_embFF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift_mem_embTF.lean](fromSumLift_mem_embTF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromSumLift_toSumLift.lean](fromSumLift_toSumLift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/lp_mem_embF.lean](lp_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/lp_prod_inv.lean](lp_prod_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/ot_mem_prod.lean](ot_mem_prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/ot_mem_prod_inv.lean](ot_mem_prod_inv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toLiftProd.lean](toLiftProd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toLiftProd_mem_embF.lean](toLiftProd_mem_embF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromLiftProd.lean](fromLiftProd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromLiftProd_mem_prod.lean](fromLiftProd_mem_prod.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/fromLiftProd_toLiftProd.lean](fromLiftProd_toLiftProd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toLiftProd_fromLiftProd.lean](toLiftProd_fromLiftProd.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/liftProdEquiv.lean](liftProdEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/toSumLift_fromSumLift.lean](toSumLift_fromSumLift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/sumLiftEquiv.lean](sumLiftEquiv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/unlift.lean](unlift.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise626/Basic.lean](Basic.lean)
