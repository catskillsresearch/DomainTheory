module

public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.projInf
public import DomainTheory.ContinuousLattice.InverseLimits.embInf
public import DomainTheory.ContinuousLattice.InverseLimits.coconeInf
public import DomainTheory.ContinuousLattice.Specialization.SpecializationLe
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.ContinuousLattices.lemma_3_9
public import DomainTheory.ContinuousLattice.ContinuousLattices.theorem_2_12
public import DomainTheory.ContinuousLattice.ContinuousLattices.theorem_2_12_more
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_continuous
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_eq_of_continuous
public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set
universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

@[reducible] noncomputable def inverseLimitTopology : TopologicalSpace (InverseLimit D P) :=
  TopologicalSpace.induced (Subtype.val : InverseLimit D P → ∀ n, D n)
    (@Pi.topologicalSpace ℕ D (fun _ => scottTopologicalSpace))

namespace inverseLimit
/-- Every coordinate projection from the explicit product/subspace inverse-limit topology is
continuous. -/
theorem coordinate_continuous (n : ℕ) :
    @Continuous (InverseLimit D P) (D n) (inverseLimitTopology D P)
      scottTopologicalSpace (fun x => x.1 n) := by
  let : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  rw [continuous_def]
  intro U hU
  rw [isOpen_induced_iff]
  exact ⟨{x : ∀ n, D n | x n ∈ U},
    (@continuous_apply ℕ D (fun _ => scottTopologicalSpace) n).isOpen_preimage U hU, rfl⟩

/-- The explicit inverse-limit topology is `T₀`, since the inclusion into the product of the
stage Scott spaces is an embedding. -/
theorem t0Space :
    @T0Space (InverseLimit D P) (inverseLimitTopology D P) := by
  let : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  let : ∀ n, T0Space (D n) := fun _ => scottTopologicalSpace.t0Space
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  have hval : Topology.IsEmbedding (Subtype.val : InverseLimit D P → ∀ n, D n) :=
    ⟨⟨rfl⟩, Subtype.val_injective⟩
  exact hval.t0Space

/-- The specialization order of the explicit inverse-limit topology is the componentwise order. -/
theorem specializationLe_iff (x y : InverseLimit D P) :
    @SpecializationLe (InverseLimit D P) (inverseLimitTopology D P) x y ↔ x ≤ y := by
  let stageOrder : ∀ n, Preorder (D n) := fun _ => inferInstance
  let limitOrder : Preorder (InverseLimit D P) := inferInstance
  let : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : ∀ n, Preorder (D n) := stageOrder
  let : Preorder (InverseLimit D P) := limitOrder
  have hval : Topology.IsEmbedding (Subtype.val : InverseLimit D P → ∀ n, D n) :=
    ⟨⟨rfl⟩, Subtype.val_injective⟩
  rw [SpecializationLe.iff_specializes, ← hval.isInducing.specializes_iff, specializes_pi]
  constructor
  · intro h n
    rw [← SpecializationLe.scott_iff, SpecializationLe.iff_specializes]
    exact h n
  · intro h n
    rw [← SpecializationLe.iff_specializes, SpecializationLe.scott_iff]
    exact h n

/-- **Scott 1972, Proposition 4.1 (injectivity step).** Coordinatewise maximal extensions
assemble to an extension into the inverse limit. Lemma 3.9 is exactly what supplies compatibility
of adjacent coordinates. -/
theorem isInjectiveSpace (hD : ∀ n, ContinuousLattice (D n)) :
    @InjectiveSpace.{u, u} (InverseLimit D P) (inverseLimitTopology D P) := by
  let stageOrder : ∀ n, Preorder (D n) := fun _ => inferInstance
  let limitOrder : Preorder (InverseLimit D P) := inferInstance
  let : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : ∀ n, Preorder (D n) := stageOrder
  let : Preorder (InverseLimit D P) := limitOrder
  constructor
  intro X Y _ _ e he f
  let fcoord (n : ℕ) (x : X) : D n := (f x).1 n
  have hfcoord (n : ℕ) : @Continuous X (D n) _ scottTopologicalSpace (fcoord n) :=
    (coordinate_continuous D P n).comp f.continuous
  let fbar (n : ℕ) : Y → D n := scottExtend e (fcoord n)
  have hfbar_cont (n : ℕ) :
      @Continuous Y (D n) _ scottTopologicalSpace (fbar n) :=
    scottExtend_continuous (hD n) e (fcoord n)
  have hfbar_compat (y : Y) (n : ℕ) :
      (P n).retr (fbar (n + 1) y) = fbar n y := by
    symm
    exact lemma_3_9 (hD n) (hD (n + 1)) (P n) e he
      (hfcoord n) (hfcoord (n + 1)) (fun x => (f x).2 n |>.symm) y
  let fbarInf (y : Y) : InverseLimit D P :=
    ⟨fun n => fbar n y, hfbar_compat y⟩
  have hfbarInf_cont :
      @Continuous Y (InverseLimit D P) _ (inverseLimitTopology D P) fbarInf := by
    change @Continuous Y (InverseLimit D P) _
      (TopologicalSpace.induced (Subtype.val : InverseLimit D P → ∀ n, D n)
        (@Pi.topologicalSpace ℕ D (fun _ => scottTopologicalSpace))) fbarInf
    rw [continuous_induced_rng]
    exact continuous_pi hfbar_cont
  refine ⟨⟨fbarInf, hfbarInf_cont⟩, fun x => ?_⟩
  apply Subtype.ext
  funext n
  exact scottExtend_eq_of_continuous (hD n) e he (fcoord n) (hfcoord n) x

/-- The Scott lattice topology constructed on `D∞` agrees with Scott's literal inverse-limit
topology: the subspace topology inherited from the Pi product of the stage Scott topologies. -/
theorem scottTopology_eq_induced_pi (hD : ∀ n, ContinuousLattice (D n)) :
    (scottTopologicalSpace : TopologicalSpace (InverseLimit D P)) =
      inverseLimitTopology D P := by
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : T0Space (InverseLimit D P) := t0Space D P
  exact (theorem_2_12.backward_exact (isInjectiveSpace D P hD)
    (specializationLe_iff D P)).2

/-- **Scott 1972, §4.** Each `x ∈ D_∞` is the (monotone) lub of its projections:
`x = ⨆ₙ i_{n∞}(xₙ)`. -/
theorem eq_iSup (x : InverseLimit D P) :
    x = ⨆ n, embInf D P n (x.1 n) := by
  have hdir := embInf_family_directed D P x
  have hne : (Set.range (fun n => embInf D P n (x.1 n))).Nonempty := Set.range_nonempty _
  refine le_antisymm ?_ ?_
  · rw [← Subtype.coe_le_coe]
    have hcoe : ((⨆ n, embInf D P n (x.1 n) : InverseLimit D P)).1
        = sSup (Subtype.val '' Set.range (fun n => embInf D P n (x.1 n))) := by
      rw [← sSup_range]
      exact coe_sSup_of_directed D P _ hne hdir
    rw [hcoe]
    intro m
    have hmem : (embInf D P m (x.1 m)).1
        ∈ Subtype.val '' Set.range (fun n => embInf D P n (x.1 n)) :=
      ⟨embInf D P m (x.1 m), ⟨m, rfl⟩, rfl⟩
    have hle := (le_sSup hmem) m
    rwa [show (embInf D P m (x.1 m)).1 m = x.1 m from iComp_self D P m (x.1 m)] at hle
  · exact iSup_le fun n => by
      rw [← Subtype.coe_le_coe]; intro m; exact iComp_incl_le D P n x m

end inverseLimit
namespace inverseLimitTopology
/-- Proposition 4.2's projection `j_{∞n}` is a continuous coordinate map for the explicit
product/subspace inverse-limit topology. -/
theorem projInf_continuous (n : ℕ) :
    @Continuous (InverseLimit D P) (D n) (inverseLimitTopology D P)
      scottTopologicalSpace (projInf D P n) :=
  inverseLimit.coordinate_continuous D P n

/-- Proposition 4.2's embedding `i_{n∞}` is also continuous for Scott's literal inverse-limit
topology, namely the subspace topology inherited from the product `∏ₘ Dₘ`. -/
theorem embInf_continuous (hD : ∀ n, ContinuousLattice (D n)) (n : ℕ) :
    @Continuous (D n) (InverseLimit D P) scottTopologicalSpace
      (inverseLimitTopology D P) (embInf D P n) := by
  rw [← inverseLimit.scottTopology_eq_induced_pi D P hD]
  exact (embInf D P n).continuous

/-- Corollary 4.3's formula `f∞(x) = ⨆ₙ fₙ(xₙ)` is continuous not only for the reconstructed Scott
topology on `D∞`, but explicitly for Scott's product/subspace inverse-limit topology. -/
theorem coconeInf_continuous (hD : ∀ n, ContinuousLattice (D n))
    {D' : Type*} [CompleteLattice D']
    (f : ∀ n, ScottMap (D n) D') :
    @Continuous (InverseLimit D P) D' (inverseLimitTopology D P)
      scottTopologicalSpace (coconeInf D P f) := by
  rw [← inverseLimit.scottTopology_eq_induced_pi D P hD]
  exact continuous_of_preservesDirectedSup (coconeInf_preservesDirectedSup D P f)

end inverseLimitTopology

end InverseLimit


end DomainTheory.ContinuousLattice
