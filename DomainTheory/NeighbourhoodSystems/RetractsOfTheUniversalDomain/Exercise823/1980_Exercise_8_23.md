# Exercise 8.23

**EXERCISE 8.23.** Suppose a construct $T$ on domains can be made into a computable operator $t : (U \to U) \to (U \to U)$ so that whenever $a : U \to U$ is a finitary projection, then so is $t(a)$ and

$$D_{t(a)} \cong T(D_a) \ .$$

Does it follow that $\|t\| = \mathrm{fix}(t)$ is such that

$$D_{\|t\|} \cong T(D_{\|t\|})$$
really is the initial solution of the domain equation with respect to projections? Since $t$ is computable, will this solution be effectively given?

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823.lean](../Exercise823.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/constMap_bot_le_idMap.lean](constMap_bot_le_idMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/eq_bot_of_fixed_constMap_bot.lean](eq_bot_of_fixed_constMap_bot.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/finitaryWitnessEquivBot.lean](finitaryWitnessEquivBot.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/fixOp.lean](fixOp.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/fixedDomain_fixOp_iso_T.lean](fixedDomain_fixOp_iso_T.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/fixedNbhd_fixOp_subsystem.lean](fixedNbhd_fixOp_subsystem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/isFinitaryProjection_constMap_bot.lean](isFinitaryProjection_constMap_bot.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/isFinitaryProjection_fixOp.lean](isFinitaryProjection_fixOp.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/isProjection_constMap_bot.lean](isProjection_constMap_bot.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/isRetraction_constMap_bot.lean](isRetraction_constMap_bot.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/iterElem_succu27.lean](iterElem_succu27.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/iterElem_zerou27.lean](iterElem_zerou27.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/rel_master_of_mem.lean](rel_master_of_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/tOp.lean](tOp.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/tOp_fixOp.lean](tOp_fixOp.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/tOp_toApproxMap.lean](tOp_toApproxMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/toApproxMap_bot_eq_constMap.lean](toApproxMap_bot_eq_constMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise823/uniqueFixedConstMapBot.lean](uniqueFixedConstMapBot.lean)
