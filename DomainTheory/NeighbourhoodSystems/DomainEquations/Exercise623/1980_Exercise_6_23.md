# Exercise 6.23

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

**Lean 4**

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
