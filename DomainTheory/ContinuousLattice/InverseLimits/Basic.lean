/-ai
This file gathers and re-exports the ingredients of the inverse limit of an ω-system of continuous lattices: compatibility and the inverse-limit type, its order and complete-lattice structure, pointwise infima and directed suprema, the tower embeddings, projections, and their composites, preservation of directed suprema, the Galois connection of a projection, Proposition 4.2, and the mediating cocone of Corollary 4.3.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Compatible
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitTopology
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitSInfCoe
public import DomainTheory.ContinuousLattice.InverseLimits.embLE
public import DomainTheory.ContinuousLattice.InverseLimits.projLE
public import DomainTheory.ContinuousLattice.InverseLimits.iComp
public import DomainTheory.ContinuousLattice.InverseLimits.embInfFun
public import DomainTheory.ContinuousLattice.InverseLimits.projInfFun
public import DomainTheory.ContinuousLattice.InverseLimits.embInf
public import DomainTheory.ContinuousLattice.InverseLimits.projInf
public import DomainTheory.ContinuousLattice.InverseLimits.proposition_4_2
public import DomainTheory.ContinuousLattice.InverseLimits.coconeInf
public import DomainTheory.ContinuousLattice.InverseLimits.projection_galoisConnection
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLT
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE_refl
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE_trans
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE_antisymm
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLT_iff_LE_not_GE
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.retr_sInf
public import DomainTheory.ContinuousLattice.InverseLimits.compatible_sInf
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.isGLB_sInf'
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.coe_sSup_of_directed
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_self
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_succ
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_self
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_succ
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_retr
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_of_le
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_of_ge
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_self
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_compatible
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_compatible
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_le
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_incl_le
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_preservesDirectedSup
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_preservesDirectedSup
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_preservesDirectedSup
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_monotone
public import DomainTheory.ContinuousLattice.InverseLimits.embInfFun_coe
public import DomainTheory.ContinuousLattice.InverseLimits.embInf_monotone
public import DomainTheory.ContinuousLattice.InverseLimits.embInf_preservesDirectedSup
public import DomainTheory.ContinuousLattice.InverseLimits.eval_preservesDirectedSup

@[expose] public section

/-!
# Inverse limits of continuous lattices (Scott 1972, §4)

We formalize Scott's **Proposition 4.1**: the inverse limit `D_∞` of an ω-system of continuous
lattices `⟨Dₙ, jₙ⟩` with each `jₙ : D_{n+1} → Dₙ` a projection is again a continuous lattice.

Scott proves this through injectivity (`D_∞` is an injective `T₀`-space, hence — Theorem 2.12 — a
continuous lattice), using the maximal-extension Proposition 3.8 and the compatibility Lemma 3.9.

* each projection `jₙ = (P n).retr` is the upper adjoint of its embedding `iₙ = (P n).incl`
  (`projection_galoisConnection`), hence preserves arbitrary infima;
* therefore the compatibility predicate is closed under pointwise `sInf`, making `D_∞` a complete
  lattice (`completeLatticeOfInf`).

For Proposition 4.1 itself we follow Scott's proof: extend every coordinate of a map into `D_∞`
maximally by Proposition 3.8, use Lemma 3.9 to make those extensions compatible, assemble the
resulting map into the inverse limit, and invoke Theorem 2.12.
-/

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))



















/-! ### Proposition 4.2: the maps `j_{∞n}` are projections

We construct Scott's embeddings `i_{n∞} : Dₙ → D_∞` and show that `⟨i_{n∞}, j_{∞n}⟩` is a
projection, where `j_{∞n}(x) = xₙ`. The component `i_{n∞}(x)_m` climbs the tower of embeddings
`iₖ = (P k).incl` for `m ≥ n` (`embLE`) and descends the tower of projections `jₖ = (P k).retr`
for `m < n` (`projLE`). -/





























/-! ### Corollary 4.3: `D_∞` is also the *direct* limit

Given continuous `fₙ : Dₙ → D'` into any complete lattice with `fₙ = f_{n+1} ∘ iₙ`, the map
`f∞(x) = ⨆ₙ fₙ(xₙ)` is the unique continuous mediating map with `fₙ = f∞ ∘ i_{n∞}`. -/

variable {D' : Type*} [CompleteLattice D']

end InverseLimit
end DomainTheory.ContinuousLattice
