module

public import DomainTheory.ContinuousLattice.Specialization.SpecializationPreorder
public import Mathlib.Topology.Order
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottFunctionEvalSubbasis
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem specializationPreorder_generateOpen (f g : C(X, Y)) (hfg : ∀ x, SpecializationPreorder (f x) (g x))
    {V : Set (C(X, Y))} (hV : GenerateOpen (scottFunctionEvalSubbasis X Y) V) (hf : f ∈ V) :
    g ∈ V :=
  match hV with
  | .basic W hW => by
    obtain ⟨x, U, hU, rfl⟩ := hW
    exact hfg x U hU hf
  | .univ => hf
  | .inter s t hs ht => by
    rcases hf with ⟨hfs, hft⟩
    exact Set.mem_inter (specializationPreorder_generateOpen f g hfg hs hfs)
      (specializationPreorder_generateOpen f g hfg ht hft)
  | .sUnion S hS => by
    obtain ⟨W, hWS, hfW⟩ := Set.mem_sUnion.mp hf
    exact Set.mem_sUnion.mpr ⟨W, hWS, specializationPreorder_generateOpen f g hfg (hS W hWS) hfW⟩

end DomainTheory.ContinuousLattice
