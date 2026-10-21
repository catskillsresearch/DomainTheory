# Exercise 6.24

**EXERCISE 6.24.** Show that there must exist domains satisfying:

$$
D \cong D + (D \times E), \quad \text{and}
$$

$$
E \cong D + E,
$$

by using a double fixed-point method. First decide what the underlying set of tokens should be, and then define $D$ and $E$ by simultaneous fixed points. (Syntactical domains as in 6.23 may very well require several simultaneous equations.)

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/Exercise624.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Dsol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Dsol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Dsol_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Dsol_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Esol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Esol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Esol_subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Esol_subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Fsol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Fsol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/GammaD.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/GammaD.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/GammaE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/GammaE.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/Gsol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/Gsol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/exists_double_fixedPoint.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/exists_double_fixedPoint.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/exists_simultaneous_subsystems.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/exists_simultaneous_subsystems.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/fTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/fTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/fTok_GammaD_GammaE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/fTok_GammaD_GammaE.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/fTok_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/fTok_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/gTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/gTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/gTok_GammaD_GammaE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/gTok_GammaD_GammaE.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/gTok_mono.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/gTok_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/master_Fsol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/master_Fsol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/master_Gsol.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/master_Gsol.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/mem_fTok_iUnion.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/mem_fTok_iUnion.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/mem_gTok_iUnion.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/mem_gTok_iUnion.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_GammaD.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_GammaD.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_GammaE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_GammaE.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_fTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_fTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_gTok.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/nil_mem_gTok.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/pIter.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/pIter.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/pIter_fst_subset_GammaD.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/pIter_fst_subset_GammaD.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise624/pIter_snd_subset_GammaE.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise624/pIter_snd_subset_GammaE.lean)
