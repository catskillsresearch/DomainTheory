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

**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/EmbedIntoPow.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/EmbedIntoPow.lean)**

@import "EmbedIntoPow.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/RecursiveCross.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/RecursiveCross.lean)**

@import "RecursiveCross.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/ratCodes.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/ratCodes.lean)**

@import "ratCodes.lean"
**[QPairCodes.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/QPairCodes.lean)**

@import "QPairCodes.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/UX.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/UX.lean)**

@import "UX.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitU.lean)**

@import "splitU.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomCode.lean)**

@import "atomCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomUCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomUCode.lean)**

@import "atomUCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/DprimeUPresentation.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/DprimeUPresentation.lean)**

@import "DprimeUPresentation.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/YseqCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/YseqCode.lean)**

@import "YseqCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomUCode_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomUCode_more.lean)**

@import "atomUCode_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/YseqCode_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/YseqCode_more.lean)**

@import "YseqCode_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/DprimeUCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/DprimeUCode.lean)**

@import "DprimeUCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/domainIsoCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/domainIsoCode.lean)**

@import "domainIsoCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem_8_8.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem_8_8.lean)**

@import "Theorem_8_8.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition_8_9.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition_8_9.lean)**

@import "Definition_8_9.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/sumMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/sumMap.lean)**

@import "sumMap.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/expMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/expMap.lean)**

@import "expMap.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/sumComb.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/sumComb.lean)**

@import "sumComb.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/arrowComb.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/arrowComb.lean)**

@import "arrowComb.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/prodComb.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/prodComb.lean)**

@import "prodComb.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition_8_10.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition_8_10.lean)**

@import "Proposition_8_10.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/TreeVal.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/TreeVal.lean)**

@import "TreeVal.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/TreeVal_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/TreeVal_more.lean)**

@import "TreeVal_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/SubsystemDomain.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/SubsystemDomain.lean)**

@import "SubsystemDomain.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_15.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_15.lean)**

@import "Exercise_8_15.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/FixedNbhdFinitaryOrder.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/FixedNbhdFinitaryOrder.lean)**

@import "FixedNbhdFinitaryOrder.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_16.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_16.lean)**

@import "Exercise_8_16.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/ProjectionCombinators.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/ProjectionCombinators.lean)**

@import "ProjectionCombinators.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_18.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_18.lean)**

@import "Exercise_8_18.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/ASharp.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/ASharp.lean)**

@import "ASharp.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/ASharp_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/ASharp_more.lean)**

@import "ASharp_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_21.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_21.lean)**

@import "Exercise_8_21.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/FixOp.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/FixOp.lean)**

@import "FixOp.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_23.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_23.lean)**

@import "Exercise_8_23.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/CoupledFixedPoints.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/CoupledFixedPoints.lean)**

@import "CoupledFixedPoints.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_24.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_24.lean)**

@import "Exercise_8_24.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitSpec812c.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitSpec812c.lean)**

@import "splitSpec812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPair812c.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPair812c.lean)**

@import "atomPair812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/XPseq812c.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/XPseq812c.lean)**

@import "XPseq812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedXY812c.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedXY812c.lean)**

@import "combinedXY812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedY812c.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedY812c.lean)**

@import "combinedY812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/hcore812c.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/hcore812c.lean)**

@import "hcore812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/transfer812c.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/transfer812c.lean)**

@import "transfer812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/transfer812c_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/transfer812c_more.lean)**

@import "transfer812c_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/domainIso812c.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/domainIso812c.lean)**

@import "domainIso812c.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/IsComputableUnion.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/IsComputableUnion.lean)**

@import "IsComputableUnion.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomE.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomE.lean)**

@import "atomE.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/IsComputableDiff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/IsComputableDiff.lean)**

@import "IsComputableDiff.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/ComputableBisection.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/ComputableBisection.lean)**

@import "ComputableBisection.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Udiff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Udiff.lean)**

@import "Udiff.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitX812e.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitX812e.lean)**

@import "splitX812e.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/xStepG.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/xStepG.lean)**

@import "xStepG.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/yStepG.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/yStepG.lean)**

@import "yStepG.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairCodeState.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairCodeState.lean)**

@import "atomPairCodeState.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairG.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairG.lean)**

@import "atomPairG.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairG_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairG_more.lean)**

@import "atomPairG_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairJunk.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/atomPairJunk.lean)**

@import "atomPairJunk.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/xPseqAtomJunk.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/xPseqAtomJunk.lean)**

@import "xPseqAtomJunk.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/xPseqAtomIdx.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/xPseqAtomIdx.lean)**

@import "xPseqAtomIdx.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/XFold.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/XFold.lean)**

@import "XFold.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/XPseqCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/XPseqCode.lean)**

@import "XPseqCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/yPseqAtomJunk.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/yPseqAtomJunk.lean)**

@import "yPseqAtomJunk.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/yPseqAtomIdx.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/yPseqAtomIdx.lean)**

@import "yPseqAtomIdx.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/YFoldInner.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/YFoldInner.lean)**

@import "YFoldInner.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/YPseqCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/YPseqCode.lean)**

@import "YPseqCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812d_early.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812d_early.lean)**

@import "effectiveIso812d_early.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812d_early_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812d_early_more.lean)**

@import "effectiveIso812d_early_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/XPseqCode_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/XPseqCode_more.lean)**

@import "XPseqCode_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/YPseqCode_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/YPseqCode_more.lean)**

@import "YPseqCode_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedCode.lean)**

@import "combinedCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/primrec812d.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/primrec812d.lean)**

@import "primrec812d.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/primrec812d_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/primrec812d_more.lean)**

@import "primrec812d_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/xPseqAtomIdx_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/xPseqAtomIdx_more.lean)**

@import "xPseqAtomIdx_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/xStepG_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/xStepG_more.lean)**

@import "xStepG_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/yPseqAtomIdx_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/yPseqAtomIdx_more.lean)**

@import "yPseqAtomIdx_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/yStepG_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/yStepG_more.lean)**

@import "yStepG_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedCode_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedCode_more.lean)**

@import "combinedCode_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/hcoreCode.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/hcoreCode.lean)**

@import "hcoreCode.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/transfer.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/transfer.lean)**

@import "transfer.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedCodeCrossFamily.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/combinedCodeCrossFamily.lean)**

@import "combinedCodeCrossFamily.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/toD1Code.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/toD1Code.lean)**

@import "toD1Code.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/toD0Code.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/toD0Code.lean)**

@import "toD0Code.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/domainIsoCode812d.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/domainIsoCode812d.lean)**

@import "domainIsoCode812d.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812d.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812d.lean)**

@import "effectiveIso812d.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitU2.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/splitU2.lean)**

@import "splitU2.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/UBisection2.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/UBisection2.lean)**

@import "UBisection2.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Vdiff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Vdiff.lean)**

@import "Vdiff.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Vunion.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Vunion.lean)**

@import "Vunion.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812_UV.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/effectiveIso812_UV.lean)**

@import "effectiveIso812_UV.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_12.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_12.lean)**

@import "Exercise_8_12.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/BooleanAlgebraFilters.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/BooleanAlgebraFilters.lean)**

@import "BooleanAlgebraFilters.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_13.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_13.lean)**

@import "Exercise_8_13.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/EmbeddingsIntoU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/EmbeddingsIntoU.lean)**

@import "EmbeddingsIntoU.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_17.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_17.lean)**

@import "Exercise_8_17.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/EmbeddingsIntoU_more.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/EmbeddingsIntoU_more.lean)**

@import "EmbeddingsIntoU_more.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/SumProdRetracts.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/SumProdRetracts.lean)**

@import "SumProdRetracts.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_19.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_19.lean)**

@import "Exercise_8_19.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/DiagonalRetracts.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/DiagonalRetracts.lean)**

@import "DiagonalRetracts.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_20.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_20.lean)**

@import "Exercise_8_20.lean"
**[ReflexiveDomain.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/ReflexiveDomain.lean)**

@import "ReflexiveDomain.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_25.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_25.lean)**

@import "Exercise_8_25.lean"
Builds a non-trivial reflexive domain $D \cong D\to D$ containing `U`.

The tip then assembles those tools into Scott’s statement.

 — `exercise_8_25`

@import "Exercise_8_25.lean"
