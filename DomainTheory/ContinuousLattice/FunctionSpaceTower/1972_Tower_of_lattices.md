# The tower of lattices

The levels of the function-space tower are $D_0$ and $D_{n+1} = [D_n \to D_n]$. `CLat` packages a complete lattice so the tower can be defined by recursion, and `towerType` is that recursion. `towerType_zero` and `towerType_succ` are the two levels, and `towerToMap` with `towerCoeFun` applies a successor level as a Scott map.

**[ContinuousLattice/FunctionSpaceTower/CLat.lean](DomainTheory/ContinuousLattice/FunctionSpaceTower/CLat.lean)**

@import "CLat.lean"
