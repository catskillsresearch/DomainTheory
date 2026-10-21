# Exercise 8.27

**EXERCISE 8.27.** (Suggested by James Donahue.)

Finite cartesian products of domains are formed by the $D_0 \times D_1$-construct we have used so often. The problem is to define — computably — some *infinite* cartesian products. In particular, as applied to the universal domain $U$, the combinator `sub` is to be regarded as a finitary projection of $U$ whose fixed points are exactly *all* the finitary projections. A map

$$d = \mathrm{sub} \circ d \circ \mathrm{sub}$$

can be regarded as a *polymorphic type* (because, whenever $t$ is a finitary projection ($=$ type), then so is $d(t)$). The *continuous product* of *all* these types would be the domain of all approximable functions $x$ such that

$$x(t) = d(t)(x(t))$$

for all types $t$. (Why does this equation mean that $x$ is in the product?) Define $\Pi$ as a combinator by

$$\Pi = \lambda d\,\lambda x\,\lambda t.\,\mathrm{sub}(d(\mathrm{sub}(t)))(x(\mathrm{sub}(t))).$$

Show that for $d$ a polymorphic type, $\Pi(d)$ is a type. (Hint: It is easy to check that $\Pi(d)$ is a projection; the problem is to show it is *finitary*.)

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/BasicInst38.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/BasicInst38.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/IsPolymorphicType.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/IsPolymorphicType.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/exists_X_of_mem_step.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/exists_X_of_mem_step.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/exists_X_of_mem_stepFun.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/exists_X_of_mem_stepFun.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/hii_hard_direction.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/hii_hard_direction.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/hii_piD.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/hii_piD.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitaryProjection_piD.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitaryProjection_piD.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitaryProjection_piDType.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitaryProjection_piDType.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitaryProjection_piD_of_formula.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitaryProjection_piD_of_formula.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitaryProjection_piU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitaryProjection_piU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitary_piU_of_formula.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitary_piU_of_formula.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitary_piU_of_isFinitary_piD.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isFinitary_piU_of_isFinitary_piD.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isProjection_piD.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isProjection_piD.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isProjection_piU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isProjection_piU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isRetraction_piD.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/isRetraction_piD.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/jArrow_comp_iArrow_apply.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/jArrow_comp_iArrow_apply.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/le_idMap_piD.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/le_idMap_piD.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piD.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piD.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDApply.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDApply.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDApply_toElementMap_eq.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDApply_toElementMap_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDType.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDType.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDTypeMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDTypeMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDType_monotone.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDType_monotone.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDUncurried.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piDUncurried.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piD_fix_of_piU_fix.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piD_fix_of_piU_fix.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piD_rel_self_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piD_rel_self_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piUFixIso.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piUFixIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piU_fix_of_piD_fix.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/piU_fix_of_piD_fix.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/scFamily.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/scFamily.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/scPrincipal.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/scPrincipal.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/subApprox_fix_of_subU_fix.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/subApprox_fix_of_subU_fix.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/subU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/subU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/subUFixIso.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/subUFixIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/subUFixIsoSubFixed.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/subUFixIsoSubFixed.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/subU_fix_of_subApprox_fix.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/subU_fix_of_subApprox_fix.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/toElementMap_piDApplyu27.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/toElementMap_piDApplyu27.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/toElementMap_piDTypeMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/toElementMap_piDTypeMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/toElementMap_piU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/toElementMap_piU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/toElementMap_subU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise827/toElementMap_subU.lean)
