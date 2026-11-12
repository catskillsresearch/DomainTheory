# Introduction

Neighbourhood systems and information systems are equivalent in a precise sense. The mathematical folklore is stronger still: all three presentations carve out the same class of domains, related by ideal completion and the Scott topology. That equivalence is already known; this article is the write-up of a machine-checked proof of the named bridges, not a first presentation of the result. The three presentations were formalized in separate libraries; the maps between them are the content of this package.

We do **not** re-prove Scott's internal theorems; we import the finished sibling packages and build cross-presentation maps:

| Presentation | Lean package | Characteristic object |
| --- | --- | --- |
| Continuous lattices [@Sco72] | `scott1972` | `ContinuousLattice D`, way-below `≪`, `ScottMap` |
| Neighbourhood systems [@Sco81] | `scott1980` | `NeighborhoodSystem`, filters as domain elements |
| Information systems [@Sco82] | `scott1982` | `InfoSys`, elements as consistent closed token sets |

The main subtlety is that a naïve reading of “domains = filters of neighbourhoods” overstates the continuous-lattice corner: for a continuous lattice `D`, the filter `{↟a | a ≤ x}` has retract `x` but properly contains the principal round filter `{↟a | a ≪ x}`. The correct identification is **`D ≃o RoundFilter`**, not raw `|𝒟|`.

@import "BridgeTheorems_Introduction.svg" {code_block=false}

The bridges are order isomorphisms of domains, and of the named construction objects, in `DomainTheory.BridgeTheorems`. They are not a 2-categorical equivalence of the full categories of continuous lattices, neighbourhood systems, and information systems with all morphisms.

The three presentation-to-presentation bridges (year labels = source → target of the packaged order isomorphism):

| Label | Years | Statement | Declaration | Note |
| --- | --- | --- | --- | --- |
| `bridge_1972_1980` | 1972 → 1980 | A continuous lattice `D` is order-isomorphic to its round way-below filters. | `continuousLattice_roundFilter_iso` (= `ContinuousLatticeToNeighborhood.domainOrderIso`) | [Round way-below filters](BridgeTheorems_Round_way_below_filters.md) / [Packaging the round-filter isomorphism](PresentationDomains/continuousLattice_roundFilter_iso.md) |
| `bridge_1980_1982` | 1980 → 1982 | Filters of a neighbourhood basis are order-isomorphic to elements of the induced information system. | `NbhdBasis.domainOrderIso` (system via `neighborhoodSystem_to_infoSys`) | [Neighbourhood bases](BridgeTheorems_Neighbourhood_bases.md) / [Neighbourhood filters and information-system elements](NeighborhoodToInfoSys/domainOrderIso.md) |
| `bridge_1982_1972` | 1982 → 1972 | Elements of an information system are order-isomorphic to ideals of its finite elements (algebraic / 1972 carrier). | `infoSys_to_idealCompletion` | [Ideals of finite elements](BridgeTheorems_Ideals_of_finite_elements.md) / [The ideal completion of an information system](InfoSysToIdealCompletion/Basic.md) |

Related companions (same chapter, not the three year-pair labels above):

| Bridge | Statement | Declaration |
| --- | --- | --- |
| 1982 → 1980 (basic opens) | An information system induces the neighbourhood system of its basic opens; elements ≃o filters of that system. | `infoSys_to_neighborhoodSystem`, `InfoSysToNeighborhood.domainOrderIso` |
| Neighbourhood system of way-below opens | The neighbourhood system associated with a continuous lattice. | `continuousLattice_to_neighborhoodSystem` |
| Algebraic lattices | An algebraic complete lattice is a continuous lattice. | `idealCompletion_to_continuousLattice` |
| Round three-way identification | For a continuous lattice with decidable equality, `D ≃o RoundInfoSysElement`, through `D ≃o RoundFilter ≃o RoundInfoSysElement`. | `presentation_domains_equiv` |

Products, sums, the function space, and Scott maps are collected under `infoSys_constructions_equiv`:

| Construction | Statement | Declaration |
| --- | --- | --- |
| Product | `\|A\| × \|B\| ≃o \|A × B\|` | `infoSys_product_domain_equiv` |
| Sum | `WithBot (\|A\| ⊕ \|B\|) ≃o \|A + B\|` | `infoSys_sum_domain_equiv` |
| Function space | Approximable maps `A → B` are order-isomorphic to the elements of the function-space system. | `infoSys_function_space_domain_equiv` |
| Scott continuity | Approximable maps `A → B` are order-isomorphic to the Scott-continuous maps on elements. | `approximableMap_scottContinuous_equiv` |
| Scott maps, round filters | Scott maps of continuous lattices are order-isomorphic to their conjugates along `D ≃o RoundFilter`. | `scottMap_roundFilter_iso` |
| Scott maps, round information systems | The same, along `presentation_domains_equiv`. | `scottMap_roundInfoSys_iso` |

On Scott’s tree domain over the lower-bound system of the natural numbers, the same carrier is an information system, a neighbourhood-filter domain, and an ideal completion, and it satisfies the equation `T ≅ A + (T × T)` as an order isomorphism of elements:

| Instance | Statement | Declaration |
| --- | --- | --- |
| Neighbourhood filters | `SexSys.Element ≃o` the filters of its basic-open neighbourhood system | `sexNeighborhoodIso` |
| Ideals | `SexSys.Element ≃o` the ideals of its finite elements | `sexIdealIso` |
| Domain equation | `SexSys.Element ≃o SexRhs.Element` | `sexDomainEquationIso` |

A full functorial equivalence, preserving products, exponentials, and inverse limits simultaneously across all three presentations, would require additional coherence theorems.

Where Scott’s 1982 text is constructive, the bridges stay constructive. Classical steps are named. The continuous-lattice identification `D ≃o RoundFilter` uses only propositional extensionality and quotient soundness: roundness is a condition on the order. An algebraic lattice is a continuous lattice by the 1972 definition of way-below, which is classical. Separated sums use classical choice for the polarity of a token (left, right, or bottom). Conjugation of Scott maps inherits that choice from the 1972 development of `ScottMap`.

Every other information-system bridge reports `Classical.choice` as well, but only because Mathlib’s `Finset` instances depend on it. A declaration whose type mentions an information system therefore prints choice even when the proof manipulates an explicit finite set and extracts no witness. That is the footprint of neighbourhood bases in both directions, of ideals of finite elements, of products and function spaces, and of approximable maps against Scott-continuous maps. The separated-sum trichotomy is a use of choice; those others are the instance frontier.

<p style="color:#15803d;margin-top:1em;">✓ <strong>Revised</strong> (2026-11-09) — <a href="../BridgeTheorems_REVISION.md">Bridge revision progress</a></p>
