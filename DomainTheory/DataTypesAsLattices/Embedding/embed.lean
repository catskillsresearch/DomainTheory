module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Continuous.Basic
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function

def embed {X : Type*} (U : ℕ → Set X) (x : X) : Pomega :=
  {n | x ∈ U n}

namespace embed

theorem continuous {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Continuous (embed U) :=
  continuous_generateFrom_iff.2 fun t ⟨n, hn⟩ => by
    subst hn
    change IsOpen (U n)
    exact hbasis.isOpen ⟨n, rfl⟩

theorem inducing {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    IsInducing (embed U) := by
  refine ⟨?_⟩
  rw [hbasis.eq_generateFrom]
  change generateFrom (Set.range U) =
    (generateFrom (Set.range memOpen)).induced (embed U)
  rw [induced_generateFrom_eq]
  congr 1
  ext V
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨memOpen n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

theorem injective {X : Type*} [TopologicalSpace X] [T0Space X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Injective (embed U) := by
  intro x y hxy
  have hmem : ∀ n, x ∈ U n ↔ y ∈ U n := fun n =>
    show n ∈ embed U x ↔ n ∈ embed U y by rw [hxy]
  refine Inseparable.eq ?_
  refine inseparable_iff_forall_isOpen.mpr ?_
  intro V hV
  constructor
  · intro hx
    obtain ⟨t, ⟨n, rfl⟩, hxt, htV⟩ :=
      hbasis.mem_nhds_iff.mp (hV.mem_nhds hx)
    exact htV ((hmem n).mp hxt)
  · intro hy
    obtain ⟨t, ⟨n, rfl⟩, hyt, htV⟩ :=
      hbasis.mem_nhds_iff.mp (hV.mem_nhds hy)
    exact htV ((hmem n).mpr hyt)

end embed

end DomainTheory.DataTypesAsLattices
