module -- shake: keep-all

import DomainTheory.DataTypesAsLattices
import DomainTheory.NeighbourhoodSystems
import DomainTheory.InformationSystems
import DomainTheory.BridgeTheorems

/-!
# DomainTheory

Root of the `DomainTheory` library: Scott domain theory assembled as a
derivative work from the five Palomar-registered per-paper
formalizations vendored under `vendor/` (see `PROVENANCE.md` and
`vendor/FROZEN.txt` for the pre-modification provenance).

* `DomainTheory.ContinuousLattice` — Scott 1972, continuous lattices
  (ex-`Scott1972.ContinuousLattice`)
* `DomainTheory.DataTypesAsLattices` — Scott 1976, data types as
  lattices (ex-`Scott1976.DataTypesAsLattices`)
* `DomainTheory.NeighbourhoodSystems` — Scott 1980 (PRG-19), neighbourhood
  systems (ex-`Scott1980.Neighborhood`)
* `DomainTheory.InformationSystems` — Scott 1982, information systems
  (ex-`Scott1982`)
* `DomainTheory.BridgeTheorems` — cross-presentation bridges
  (ex-`ScottModels`)
-/
