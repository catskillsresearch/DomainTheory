# Exercise 8.25

**EXERCISE 8.25.** The problem is to find non-trivial solutions to the domain equation
$$
(\spadesuit) \qquad D \cong D \to D.
$$
Show that the "obvious" solution by retracts is of no use because
$$
1 \to 1 = 1
$$
for projections. Change the method as follows. Show first
$$
U^\infty \times U^\infty \cong U^\infty.
$$
Next solve
$$
D \cong D \to U^\infty
$$
and remark that $U \triangleleft D$; so $D$ is universal and non-trivial. Finally prove $(\spadesuit)$ for this $D$. (Hint: First show
$$
D \times D \cong D,
$$
and then show $D$ satisfies $(\spadesuit)$.) Is this $D$ effectively given?

## Tip summary

The tip asserts existence of a non-trivial domain isomorphic to its function space and containing `U`.

## Development

Rational-interval coding used by effective presentations.

**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/EmbedIntoPow.lean](EmbedIntoPow.lean)**

@import "EmbedIntoPow.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/RecursiveCross.lean](RecursiveCross.lean)**

@import "RecursiveCross.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/ratCodes.lean](ratCodes.lean)**

@import "ratCodes.lean"
**[QPairCodes.lean](QPairCodes.lean)**

@import "QPairCodes.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/UX.lean](UX.lean)**

@import "UX.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitU.lean](splitU.lean)**

@import "splitU.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomCode.lean](atomCode.lean)**

@import "atomCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomUCode.lean](atomUCode.lean)**

@import "atomUCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/DprimeUPresentation.lean](DprimeUPresentation.lean)**

@import "DprimeUPresentation.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/YseqCode.lean](YseqCode.lean)**

@import "YseqCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomUCode_more.lean](atomUCode_more.lean)**

@import "atomUCode_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/YseqCode_more.lean](YseqCode_more.lean)**

@import "YseqCode_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/DprimeUCode.lean](DprimeUCode.lean)**

@import "DprimeUCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/domainIsoCode.lean](domainIsoCode.lean)**

@import "domainIsoCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem_8_8.lean](Theorem_8_8.lean)**

@import "Theorem_8_8.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition_8_9.lean](Definition_8_9.lean)**

@import "Definition_8_9.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/sumMap.lean](sumMap.lean)**

@import "sumMap.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/expMap.lean](expMap.lean)**

@import "expMap.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/sumComb.lean](sumComb.lean)**

@import "sumComb.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/arrowComb.lean](arrowComb.lean)**

@import "arrowComb.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/prodComb.lean](prodComb.lean)**

@import "prodComb.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition_8_10.lean](Proposition_8_10.lean)**

@import "Proposition_8_10.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/TreeVal.lean](TreeVal.lean)**

@import "TreeVal.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/TreeVal_more.lean](TreeVal_more.lean)**

@import "TreeVal_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/SubsystemDomain.lean](SubsystemDomain.lean)**

@import "SubsystemDomain.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_15.lean](Exercise_8_15.lean)**

@import "Exercise_8_15.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/FixedNbhdFinitaryOrder.lean](FixedNbhdFinitaryOrder.lean)**

@import "FixedNbhdFinitaryOrder.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_16.lean](Exercise_8_16.lean)**

@import "Exercise_8_16.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/ProjectionCombinators.lean](ProjectionCombinators.lean)**

@import "ProjectionCombinators.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_18.lean](Exercise_8_18.lean)**

@import "Exercise_8_18.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/ASharp.lean](ASharp.lean)**

@import "ASharp.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/ASharp_more.lean](ASharp_more.lean)**

@import "ASharp_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_21.lean](Exercise_8_21.lean)**

@import "Exercise_8_21.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/FixOp.lean](FixOp.lean)**

@import "FixOp.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_23.lean](Exercise_8_23.lean)**

@import "Exercise_8_23.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/CoupledFixedPoints.lean](CoupledFixedPoints.lean)**

@import "CoupledFixedPoints.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_24.lean](Exercise_8_24.lean)**

@import "Exercise_8_24.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitSpec812c.lean](splitSpec812c.lean)**

@import "splitSpec812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPair812c.lean](atomPair812c.lean)**

@import "atomPair812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/XPseq812c.lean](XPseq812c.lean)**

@import "XPseq812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedXY812c.lean](combinedXY812c.lean)**

@import "combinedXY812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedY812c.lean](combinedY812c.lean)**

@import "combinedY812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/hcore812c.lean](hcore812c.lean)**

@import "hcore812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/transfer812c.lean](transfer812c.lean)**

@import "transfer812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/transfer812c_more.lean](transfer812c_more.lean)**

@import "transfer812c_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/domainIso812c.lean](domainIso812c.lean)**

@import "domainIso812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/IsComputableUnion.lean](IsComputableUnion.lean)**

@import "IsComputableUnion.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomE.lean](atomE.lean)**

@import "atomE.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/IsComputableDiff.lean](IsComputableDiff.lean)**

@import "IsComputableDiff.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/ComputableBisection.lean](ComputableBisection.lean)**

@import "ComputableBisection.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Udiff.lean](Udiff.lean)**

@import "Udiff.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitX812e.lean](splitX812e.lean)**

@import "splitX812e.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/xStepG.lean](xStepG.lean)**

@import "xStepG.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/yStepG.lean](yStepG.lean)**

@import "yStepG.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairCodeState.lean](atomPairCodeState.lean)**

@import "atomPairCodeState.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairG.lean](atomPairG.lean)**

@import "atomPairG.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairG_more.lean](atomPairG_more.lean)**

@import "atomPairG_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairJunk.lean](atomPairJunk.lean)**

@import "atomPairJunk.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/xPseqAtomJunk.lean](xPseqAtomJunk.lean)**

@import "xPseqAtomJunk.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/xPseqAtomIdx.lean](xPseqAtomIdx.lean)**

@import "xPseqAtomIdx.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/XFold.lean](XFold.lean)**

@import "XFold.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/XPseqCode.lean](XPseqCode.lean)**

@import "XPseqCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/yPseqAtomJunk.lean](yPseqAtomJunk.lean)**

@import "yPseqAtomJunk.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/yPseqAtomIdx.lean](yPseqAtomIdx.lean)**

@import "yPseqAtomIdx.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/YFoldInner.lean](YFoldInner.lean)**

@import "YFoldInner.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/YPseqCode.lean](YPseqCode.lean)**

@import "YPseqCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812d_early.lean](effectiveIso812d_early.lean)**

@import "effectiveIso812d_early.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812d_early_more.lean](effectiveIso812d_early_more.lean)**

@import "effectiveIso812d_early_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/XPseqCode_more.lean](XPseqCode_more.lean)**

@import "XPseqCode_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/YPseqCode_more.lean](YPseqCode_more.lean)**

@import "YPseqCode_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedCode.lean](combinedCode.lean)**

@import "combinedCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/primrec812d.lean](primrec812d.lean)**

@import "primrec812d.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/primrec812d_more.lean](primrec812d_more.lean)**

@import "primrec812d_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/xPseqAtomIdx_more.lean](xPseqAtomIdx_more.lean)**

@import "xPseqAtomIdx_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/xStepG_more.lean](xStepG_more.lean)**

@import "xStepG_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/yPseqAtomIdx_more.lean](yPseqAtomIdx_more.lean)**

@import "yPseqAtomIdx_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/yStepG_more.lean](yStepG_more.lean)**

@import "yStepG_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedCode_more.lean](combinedCode_more.lean)**

@import "combinedCode_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/hcoreCode.lean](hcoreCode.lean)**

@import "hcoreCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/transfer.lean](transfer.lean)**

@import "transfer.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedCodeCrossFamily.lean](combinedCodeCrossFamily.lean)**

@import "combinedCodeCrossFamily.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/toD1Code.lean](toD1Code.lean)**

@import "toD1Code.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/toD0Code.lean](toD0Code.lean)**

@import "toD0Code.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/domainIsoCode812d.lean](domainIsoCode812d.lean)**

@import "domainIsoCode812d.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812d.lean](effectiveIso812d.lean)**

@import "effectiveIso812d.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitU2.lean](splitU2.lean)**

@import "splitU2.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/UBisection2.lean](UBisection2.lean)**

@import "UBisection2.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Vdiff.lean](Vdiff.lean)**

@import "Vdiff.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Vunion.lean](Vunion.lean)**

@import "Vunion.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812_UV.lean](effectiveIso812_UV.lean)**

@import "effectiveIso812_UV.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_12.lean](Exercise_8_12.lean)**

@import "Exercise_8_12.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/BooleanAlgebraFilters.lean](BooleanAlgebraFilters.lean)**

@import "BooleanAlgebraFilters.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_13.lean](Exercise_8_13.lean)**

@import "Exercise_8_13.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/EmbeddingsIntoU.lean](EmbeddingsIntoU.lean)**

@import "EmbeddingsIntoU.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_17.lean](Exercise_8_17.lean)**

@import "Exercise_8_17.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/EmbeddingsIntoU_more.lean](EmbeddingsIntoU_more.lean)**

@import "EmbeddingsIntoU_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/SumProdRetracts.lean](SumProdRetracts.lean)**

@import "SumProdRetracts.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_19.lean](Exercise_8_19.lean)**

@import "Exercise_8_19.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/DiagonalRetracts.lean](DiagonalRetracts.lean)**

@import "DiagonalRetracts.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_20.lean](Exercise_8_20.lean)**

@import "Exercise_8_20.lean"
**[ReflexiveDomain.lean](ReflexiveDomain.lean)**

@import "ReflexiveDomain.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_25.lean](Exercise_8_25.lean)**

@import "Exercise_8_25.lean"
Builds a non-trivial reflexive domain $D \cong D\to D$ containing `U`.

The tip then assembles those tools into Scott’s statement.

 — `exercise_8_25`

@import "Exercise_8_25.lean"
