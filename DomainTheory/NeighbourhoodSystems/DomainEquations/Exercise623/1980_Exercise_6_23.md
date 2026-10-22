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

- [NeighbourhoodSystems/DomainEquations/Exercise623/gFix.lean](gFix.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFix_fixed.lean](gFix_fixed.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFix_nil_mem.lean](gFix_nil_mem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFix_nonempty.lean](gFix_nonempty.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gGen.lean](gGen.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gGen_master.lean](gGen_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gBase.lean](gBase.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower.lean](gTower.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower_zero.lean](gTower_zero.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower_succ.lean](gTower_succ.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gChain.lean](gChain.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower_le.lean](gTower_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower_master.lean](gTower_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gColim.lean](gColim.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/mem_gColim.lean](mem_gColim.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gColim_master.lean](gColim_master.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Texp.lean](Texp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Texp_rooted.lean](Texp_rooted.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Exp.lean](Exp.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/ext.lean](ext.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/BasicInst28.lean](BasicInst28.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gTower_sub_colim.lean](gTower_sub_colim.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gColim_obj_sys_eq.lean](gColim_obj_sys_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gColim_obj_eq.lean](gColim_obj_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Exp_structure_eq.lean](Exp_structure_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/id_val.lean](id_val.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/comp_val.lean](comp_val.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFunctorMap.lean](gFunctorMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFunctor.lean](gFunctor.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFunctor_obj.lean](gFunctor_obj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gFunctorMap_val.lean](gFunctorMap_val.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/TexpF.lean](TexpF.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/algStr.lean](algStr.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/algStr_strict.lean](algStr_strict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/isoOfObjEq.lean](isoOfObjEq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/ExpIso.lean](ExpIso.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/ExpAlg.lean](ExpAlg.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expHom.lean](expHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expInv.lean](expInv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel.lean](descRel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel_succ.lean](descRel_succ.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/algHom_ext.lean](algHom_ext.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/constBot_le.lean](constBot_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel_le_succ.lean](descRel_le_succ.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel_mono.lean](descRel_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descDir.lean](descDir.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descDirLe.lean](descDirLe.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap.lean](descMap.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_is_sup.lean](descMap_is_sup.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_fix.lean](descMap_fix.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_rel.lean](descMap_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expInv_comp_expHom.lean](expInv_comp_expHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descComm.lean](descComm.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expInv_strict.lean](expInv_strict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel_isStrict.lean](descRel_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_isStrict.lean](descMap_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descAlgHom.lean](descAlgHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expSub.lean](expSub.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/inj_isStrict.lean](inj_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/isoOfObjEq_hom_rel.lean](isoOfObjEq_hom_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expHom_rel.lean](expHom_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/isoOfObjEq_inv_rel.lean](isoOfObjEq_inv_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expInv_rel.lean](expInv_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/oplusMapTok_inj.lean](oplusMapTok_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/oplusMapTok_proj.lean](oplusMapTok_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/otimesMapTok_inj.lean](otimesMapTok_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/otimesMapTok_proj.lean](otimesMapTok_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/prodMapTok_inj.lean](prodMapTok_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/prodMapTok_proj.lean](prodMapTok_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/rho.lean](rho.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/rho_rel.lean](rho_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/rho_mono.lean](rho_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/iSupRho.lean](iSupRho.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/iSupRho_eq_id.lean](iSupRho_eq_id.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/rho_zero_rel.lean](rho_zero_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gcomp_rho_zero.lean](gcomp_rho_zero.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/self_inj.lean](self_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/self_proj.lean](self_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/sumMapTok_inj.lean](sumMapTok_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/map_inj.lean](map_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/sumMapTok_proj.lean](sumMapTok_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/map_proj.lean](map_proj.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/map_rho_eq.lean](map_rho_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/key_rho.lean](key_rho.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gcomp_rho_succ.lean](gcomp_rho_succ.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/gcomp_rho_eq.lean](gcomp_rho_eq.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_eq_algHom.lean](descMap_eq_algHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/ExpInitial.lean](ExpInitial.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/Subsystemu2eproj_isStrict.lean](Subsystemu2eproj_isStrict.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/expHom_comp_expInv.lean](expHom_comp_expInv.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/algHom_fix.lean](algHom_fix.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descRel_le_algHom.lean](descRel_le_algHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623/descMap_le_algHom.lean](descMap_le_algHom.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise623.lean](../Exercise623.lean)
