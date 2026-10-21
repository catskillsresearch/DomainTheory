/-ai
This file gathers and re-exports the function-space tower used for Scott's Theorem 4.4: the bundled complete lattices and the recursively defined levels, conjugation of Scott maps, the inclusion and retraction of a function space and the tower projections, the inverse limit and its function space, the summands of the two limit maps, and the comparison, monotonicity, and inverse lemmas that identify the limit with its function space. It also registers the complete-lattice structure carried by a bundled lattice as a type-class instance.
ai-/
module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerCLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMapFun
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclFun
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrFun
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceProjection
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_orderIso
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_scottTopology_homeomorph
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_sourceTopology_homeomorph
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap_coe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclFun_continuous
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclFun_outer_continuous
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrFun_continuous
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrFun_outer_continuous
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrIncl
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclRetrLe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj_succ_retr_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInfFn
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_iSup
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInf_succ_iSup
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conj_iInfTerm_eq
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.incl_projInf_le_projInf_succ
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_le_succ
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_monotone
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iSup₂_monotone_eq_diagonal
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_incl_le_conjMap_succ
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf_embInfInf_eq
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf_comp_embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj_retr_conjMap_succ
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf_comp_projInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf_embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf_projInfInf

@[expose] public section

/-!
# The function-space tower and Theorem 4.4
(Scott 1972; wording from `sources/ScottContinLatt1972.md`)

Scott, just above Theorem 4.4: let \(D = D_0\) be a given continuous lattice; make
\(D_0\) a projection of \(D_1 = [D_0 \to D_0]\) by a pair \(i_0, j_0\) (Proposition 3.13);
define recursively \(D_{n+1} = [D_n \to D_n]\) and introduce \(i_{n+1}, j_{n+1}\) by
Proposition 3.7, so \(j_{n+1} = [j_n \to j_n]\).

**4.4 Theorem.** *The inverse limit \(D_\infty\) of the recursively defined sequence
\(\langle D_n, j_n \rangle_{n=0}^{\infty}\) of function spaces is not only a continuous
lattice, but it is also homeomorphic to its own function space \([D_\infty \to D_\infty]\).*
-/

namespace DomainTheory.ContinuousLattice

universe u


attribute [instance] CLat.str








/-! ### Conjugation used in Scott's §4 limit formulas

Theorem 4.4 uses maps of the form `f ↦ post ∘ f ∘ pre`.  We bundle this operation as a Scott map;
its continuity follows because directed suprema in function spaces are computed pointwise
(Theorem 3.3). -/

section Conj

open Set

variable {Y Z W : Type u} [CompleteLattice Y] [CompleteLattice Z] [CompleteLattice W]





end Conj











section Tower

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))


end Tower

/-! ### Theorem 4.4(a): the limit maps `i_∞` and `j_∞`

We now wire the concrete inverse limit `D_∞` of the function-space tower and write down Scott's pair

```
i_∞(x) = ⨆ₙ (i_{n∞} ∘ x_{n+1} ∘ j_{∞n})      : D_∞ → [D_∞ → D_∞]
j_∞(f) = ⨆ₙ i_{(n+1)∞}(j_{∞n} ∘ f ∘ i_{n∞})  : [D_∞ → D_∞] → D_∞
```

Each summand is itself a Scott map (a composite of `conjMap`, `embInf`, `projInf`), so each of
`i_∞`, `j_∞` is a *supremum of Scott maps* and is therefore Scott-continuous automatically: by
Theorem 3.3 the function space `[A → B]` is a complete lattice in which suprema are computed
pointwise. No bespoke continuity argument is needed. -/

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))











/-! ### Theorem 4.4(b): `j_∞ ∘ i_∞ = id` on `D_∞`

Scott's calculation (~lines 1290–1294): expand `j_∞(i_∞(x))` as a double sup, collapse the monotone
double limit to the diagonal using `projInf ∘ embInf = id` on each summand, then recognize `x` via
`inverseLimit_eq_iSup` (with a one-step index shift). -/

section Thm44b

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))











/-! ### Theorem 4.4(c): `i_∞ ∘ j_∞ = id` on `[D_∞ → D_∞]`

This is the converse half (Scott ~lines 1322–1335). The restrictions
`u_n = j_{∞n} ∘ f ∘ i_{n∞} ∈ D_{n+1}` satisfy the Lemma-4.5 recursion `j_{n+1}(u_{n+2}) = u_{n+1}`
(`towerProj_retr_conjMap_succ`), so Lemma 4.5 identifies the components of `j_∞(f)`. Expanding
`i_∞(j_∞(f))` then yields the approximation `⨆ₙ rₙ ∘ f ∘ rₙ` with `rₙ = i_{n∞} ∘ j_{∞n}`, and the
functional equation `id = ⨆ₙ rₙ` (via `inverseLimit_eq_iSup`) plus continuity of `f` collapse this
to `f`. -/



end Thm44b

/-! ### Theorem 4.4(d): `D_∞` is homeomorphic to `[D_∞ → D_∞]`

Scott's statement of Theorem 4.4 is the homeomorphism. The maps `i_∞` and `j_∞` from (b) and (c)
are mutually inverse and Scott-continuous (bundled `ScottMap`s), so they are that homeomorphism. -/

section Thm44d

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))





end Thm44d
end LimitMaps
end DomainTheory.ContinuousLattice
