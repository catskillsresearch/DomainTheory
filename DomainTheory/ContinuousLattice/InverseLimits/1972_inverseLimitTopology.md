# inverseLimitTopology

`inverseLimitTopology` is the subspace topology induced on threads by the product of the stage Scott topologies. The same file then opens `namespace inverseLimit` for the properties of the limit in that topology, and `namespace inverseLimitTopology` for continuity of the stage embedding, the limit projection, and the mediating map. Those continuity theorems call `inverseLimit.coordinate_continuous` and `inverseLimit.scottTopology_eq_induced_pi`, so the two namespaces are one module.

**[ContinuousLattice/InverseLimits/inverseLimitTopology.lean](DomainTheory/ContinuousLattice/InverseLimits/inverseLimitTopology.lean)**

@import "inverseLimitTopology.lean"
