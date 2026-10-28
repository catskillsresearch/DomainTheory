module

public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_mono
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_le
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_eq
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_def
public import DomainTheory.ContinuousLattice.FunctionSpaces.preservesDirectedSup_coe
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace Proposition314

theorem fix_preservesDirectedSup : PreservesDirectedSup (fix : ScottMap D D → D) := by
  intro S hSne hSdir
  set T : Set D := Set.image fix S with hTdef
  have hTne : T.Nonempty := hSne.image fix
  have hTdir : DirectedOn (· ≤ ·) T := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
    obtain ⟨h, hh, hfh, hf'h⟩ := hSdir f hf f' hf'
    exact ⟨fix h, Set.mem_image_of_mem fix hh, fix_mono hfh, fix_mono hf'h⟩
  show fix (sSup S) = sSup T
  apply le_antisymm
  · apply fix_le
    show ((sSup S : ScottMap D D) : D → D) (sSup T) ≤ sSup T
    rw [ScottMap.sSup_apply]
    apply sSup_le
    rintro _ ⟨f, hf, rfl⟩
    show (f : D → D) (sSup T) ≤ sSup T
    rw [f.preservesDirectedSup_coe T hTne hTdir]
    apply sSup_le
    rintro _ ⟨_, ⟨f', hf', rfl⟩, rfl⟩
    obtain ⟨h, hh, hfh, hf'h⟩ := hSdir f hf f' hf'
    calc (f : D → D) (fix f')
        ≤ (h : D → D) (fix f') := ScottMap.le_def.mp hfh (fix f')
      _ ≤ (h : D → D) (fix h) := h.monotone (fix_mono hf'h)
      _ = fix h := fix_eq h
      _ ≤ sSup T := le_sSup (Set.mem_image_of_mem fix hh)
  · apply sSup_le
    rintro _ ⟨f, hf, rfl⟩
    exact fix_mono (le_sSup hf)

end Proposition314

end DomainTheory.ContinuousLattice
