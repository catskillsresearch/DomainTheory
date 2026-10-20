module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_genPoint_isClopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.self_mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.isOpen_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_genPoint_biUnion

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems









/-- **`8.13(c1)`.** Cantor space's clopen algebra is exactly `GeneratedBy genPoint` — the free
Boolean algebra on `ℵ₀` generators (`8.13(a)`), transported to carrier `ℕ → Bool`. -/
theorem isClopen_iff_generatedBy_genPoint {Y : Set (ℕ → Bool)} :
    IsClopen Y ↔ GeneratedBy genPoint Y := by
  refine ⟨fun hY => ?_, generatedBy_genPoint_isClopen⟩
  classical
  have hbox : ∀ f ∈ Y, ∃ I : Finset ℕ, box I f ⊆ Y := by
    intro f hf
    obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hY.isOpen f hf
    refine ⟨I, fun x hx => hIu fun i hi => ?_⟩
    rw [hx i hi]
    exact (hu i hi).2
  choose Ifn hIfn using hbox
  set Ig : Y → Finset ℕ := fun f => Ifn (f : ℕ → Bool) f.2
  set fg : Y → ℕ → Bool := fun f => (f : ℕ → Bool)
  have hcover : Y ⊆ ⋃ f : Y, box (Ig f) (fg f) :=
    fun f hf => Set.mem_iUnion.mpr ⟨⟨f, hf⟩, self_mem_box _ _⟩
  have hcompact : IsCompact Y := hY.isClosed.isCompact
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover (fun f : Y => box (Ig f) (fg f))
    (fun f => isOpen_box _ _) hcover
  have heq : Y = ⋃ f ∈ t, box (Ig f) (fg f) := by
    refine Set.Subset.antisymm ht (Set.iUnion₂_subset fun f _ => hIfn (f : ℕ → Bool) f.2)
  rw [heq]
  exact generatedBy_genPoint_biUnion t Ig fg

end DomainTheory.NeighbourhoodSystems
